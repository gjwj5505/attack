# insert_images.ps1
# Inserts the prepared images into SigPL_new.pptx at positions anchored to
# the user's red-text placeholder markers. Existing shapes are not touched.
#
# For each row: find the first text shape whose text contains `keyword`,
# then place the image below it at the given width (aspect preserved).
# `dx`/`dy` shift the image relative to the anchor's bottom-left corner.
#
# Coordinate unit is POINTS (1pt = 1/72"). PowerPoint COM's HasText returns
# msoTrue = -1, not $true — hence the [int] cast.

$ErrorActionPreference = 'Stop'

$here     = Split-Path -Parent $MyInvocation.MyCommand.Path
$pptxPath = Join-Path $here 'SigPL_new.pptx'
$imgDir   = Join-Path $here 'snt_pages'

$insertions = @(
  # §01 - attack example (marker [87])
  @{ keyword = 'SnT때 썼던 공격 예시';                image = 'attack_example_body.png'; width = 500; dx = -50; dy = 15 }

  # §03 - two images from one marker [89]; stack side-by-side below it
  @{ keyword = '비결정성에 의해 잘못 공격한 예시';    image = 'nondet_attack_body.png';  width = 360; dx = 0;   dy = 15 }
  @{ keyword = '비결정성을 없앤 언어가 CIL';          image = 'c_nondet_body.png';       width = 360; dx = 380; dy = 15 }

  # §04 - big merged proof-tree figure (marker [82])
  @{ keyword = '그림 좀더 크고';                     image = 'merge_trees.png';         width = 700; dx = -300; dy = 15 }

  # §05 - two examples (markers [92], [91])
  @{ keyword = '실행의미가 커지는 예시';             image = 'size_semantics_big.png';  width = 360; dx = 0;   dy = 15 }
  @{ keyword = '프로그램이 커지는 예시';             image = 'size_prog_big.png';       width = 200; dx = 60;  dy = 15 }

  # §06 - unification code panels (marker [83])
  @{ keyword = 'unification이 일어나는 예시';        image = 'unify_example.png';       width = 700; dx = -430; dy = 15 }
)

function Has-Text($sh) {
  try { return ([int]$sh.HasTextFrame -eq -1) } catch { return $false }
}

Write-Host "opening PowerPoint..." -ForegroundColor Cyan
$ppt = New-Object -ComObject PowerPoint.Application
$ppt.Visible = [Microsoft.Office.Core.MsoTriState]::msoTrue
$deck = $ppt.Presentations.Open($pptxPath, $false, $false, $true)
$slide = $deck.Slides.Item(1)

foreach ($ins in $insertions) {
  $keyword = $ins.keyword
  $imgFile = Join-Path $imgDir $ins.image
  if (-not (Test-Path $imgFile)) {
    Write-Warning ("missing image: {0}" -f $imgFile); continue
  }

  # find the text-bearing shape whose text contains the keyword
  $anchor = $null
  foreach ($sh in $slide.Shapes) {
    if (-not (Has-Text $sh)) { continue }
    try {
      $tr = $sh.TextFrame.TextRange
      if ($tr.Length -eq 0) { continue }
      $t = $tr.Text
    } catch { continue }
    if ($t -and $t.IndexOf($keyword) -ge 0) { $anchor = $sh; break }
  }

  if ($null -eq $anchor) {
    Write-Warning ("marker not found: '{0}' -- skipping {1}" -f $keyword, $ins.image)
    continue
  }

  $left = $anchor.Left + [double]$ins.dx
  $top  = $anchor.Top + $anchor.Height + [double]$ins.dy
  $w    = [double]$ins.width

  $pic = $slide.Shapes.AddPicture(
    $imgFile,
    [Microsoft.Office.Core.MsoTriState]::msoFalse,
    [Microsoft.Office.Core.MsoTriState]::msoTrue,
    $left, $top, $w, -1)

  Write-Host ("  inserted {0,-28} under '{1}' at L={2:F0} T={3:F0} W={4}" -f `
              $ins.image, $keyword, $left, $top, $w) -ForegroundColor Green
}

$deck.Save()
$deck.Close()
$ppt.Quit()
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($slide) | Out-Null
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($deck)  | Out-Null
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($ppt)   | Out-Null
[System.GC]::Collect(); [System.GC]::WaitForPendingFinalizers()

Write-Host "done." -ForegroundColor Cyan
