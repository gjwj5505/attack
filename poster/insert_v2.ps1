# insert_v2.ps1
#
# Inserts the xelatex-rendered PNGs (SnT PDF pages + tikz figures) into
# SigPL_new.pptx at carefully chosen positions per section. Deletes the
# red-text placeholder markers as their content is placed. Leaves everything
# else alone so user's manual edits are preserved.

$ErrorActionPreference = 'Stop'

$here     = Split-Path -Parent $MyInvocation.MyCommand.Path
$pptxPath = Join-Path $here 'SigPL_new.pptx'
$imgDir   = Join-Path $here 'snt_pages'

# ---------- palette ----------
function RGB([int]$r, [int]$g, [int]$b) { return $r + (256 * $g) + (65536 * $b) }
$Faint = RGB 124 138 153
$Deep  = RGB 0   57  127

# ---------- image-anchored placements ----------
# One row per image. `x`, `y` are absolute PowerPoint points. `w` is width;
# height is preserved via aspect ratio (h=-1 in AddPicture).
$images = @(
  # §01 - SnT attack example (col1: 74..815)
  @{ file = 'attack_example_body.png';  x = 200; y = 740;  w = 440 }

  # §03 - formula image (col1)
  @{ file = 'attack_formula.png';       x =  95; y = 1155; w = 660 }

  # §03 - nondet diagrams + C nondet table (col1, side by side, slight overflow)
  @{ file = 'nondet_attack_body.png';   x =  74; y = 1395; w = 320 }
  @{ file = 'c_nondet_body.png';        x = 420; y = 1395; w = 380 }

  # §04 - merged proof-tree figure (col2: 869..1610)
  @{ file = 'merge_trees.png';          x = 869; y = 1245; w = 720 }

  # §05 - two size examples (col1, side by side)
  @{ file = 'size_semantics_big.png';   x =  74; y = 1780; w = 340 }
  @{ file = 'size_program_big.png';     x = 430; y = 1780; w = 340 }

  # §06 - unification code panels (col2)
  @{ file = 'unify_example.png';        x = 869; y = 2000; w = 720 }
)

# ---------- red-text markers to delete once their asset is placed ----------
$markersToDelete = @(
  'SnT때 썼던 공격 예시'
  '수식으로 예쁘게 쓰자'
  'SnT때 썼던, 비결정성에 의해'
  '그림 좀더 크고'
  'SnT때 썼던, 실행의미가 커지는'
  'SnT때 썼던, 프로그램이 커지는'
  'unification이 일어나는 예시'
)

# ---------- old §04 diagram to delete (identified by position) ----------
# Shape [81] "증명나무 바구니" at L=950 T=1250 W=339 H=263 — a Picture.
$oldDiagramFilter = @{ minLeft = 940; maxLeft = 960; minTop = 1240; maxTop = 1260 }

# ---------- helpers ----------
function Has-Text($sh) {
  try { return ([int]$sh.HasTextFrame -eq -1) } catch { return $false }
}
function Get-Text($sh) {
  try { $tr = $sh.TextFrame.TextRange; if ($tr.Length -gt 0) { return $tr.Text } } catch {}
  return ''
}

# ---------- open PPT ----------
Write-Host "opening PowerPoint..." -ForegroundColor Cyan
$ppt = New-Object -ComObject PowerPoint.Application
$ppt.Visible = [Microsoft.Office.Core.MsoTriState]::msoTrue
$deck = $ppt.Presentations.Open($pptxPath, $false, $false, $true)
$slide = $deck.Slides.Item(1)

# ---------- delete red markers ----------
Write-Host "removing red-text markers..." -ForegroundColor Cyan
$toDelete = @()
foreach ($sh in $slide.Shapes) {
  if (-not (Has-Text $sh)) { continue }
  $t = Get-Text $sh
  foreach ($m in $markersToDelete) {
    if ($t -and $t.IndexOf($m) -ge 0) {
      $toDelete += @{ id = $sh.Id; hint = $m }
      break
    }
  }
}
foreach ($d in $toDelete) {
  foreach ($sh in $slide.Shapes) {
    if ($sh.Id -eq $d.id) {
      Write-Host ("  deleted marker: {0}" -f $d.hint) -ForegroundColor DarkGray
      $sh.Delete()
      break
    }
  }
}

# ---------- delete old §04 diagram ----------
Write-Host "removing old §04 diagram..." -ForegroundColor Cyan
$oldIds = @()
foreach ($sh in $slide.Shapes) {
  # msoPicture = 13
  if ([int]$sh.Type -ne 13) { continue }
  if ($sh.Left -ge $oldDiagramFilter.minLeft -and $sh.Left -le $oldDiagramFilter.maxLeft `
      -and $sh.Top -ge $oldDiagramFilter.minTop -and $sh.Top -le $oldDiagramFilter.maxTop) {
    $oldIds += $sh.Id
  }
}
foreach ($id in $oldIds) {
  foreach ($sh in $slide.Shapes) {
    if ($sh.Id -eq $id) {
      Write-Host ("  deleted picture at L={0} T={1}" -f [int]$sh.Left, [int]$sh.Top) -ForegroundColor DarkGray
      $sh.Delete()
      break
    }
  }
}

# ---------- insert images ----------
Write-Host "inserting images..." -ForegroundColor Cyan
foreach ($im in $images) {
  $path = Join-Path $imgDir $im.file
  if (-not (Test-Path $path)) { Write-Warning "missing $path"; continue }
  # get natural pixel dimensions from the file so we can compute height that
  # preserves aspect ratio (AddPicture with H=-1 is unreliable across builds)
  Add-Type -AssemblyName System.Drawing
  $img = [System.Drawing.Image]::FromFile($path)
  $ar  = [double]$img.Height / [double]$img.Width
  $img.Dispose()
  $h  = [double]$im.w * $ar

  $pic = $slide.Shapes.AddPicture(
    $path,
    [Microsoft.Office.Core.MsoTriState]::msoFalse,
    [Microsoft.Office.Core.MsoTriState]::msoTrue,
    [double]$im.x, [double]$im.y, [double]$im.w, $h)
  # lock aspect + resize once more, defensively
  $pic.LockAspectRatio = [Microsoft.Office.Core.MsoTriState]::msoTrue
  $pic.Width = [double]$im.w
  $pic.AlternativeText = "poster_insert:" + $im.file
  Write-Host ("  {0,-30} L={1,4} T={2,4} W={3,4} H={4,4}" -f `
              $im.file, [int]$pic.Left, [int]$pic.Top, [int]$pic.Width, [int]$pic.Height) `
              -ForegroundColor Green
}

# ---------- add native caption under formula ----------
Write-Host "adding formula caption..." -ForegroundColor Cyan
$cap = $slide.Shapes.AddTextbox(1, 95, 1220, 660, 24)
$cap.TextFrame2.TextRange.Text = "분석기가 위치·변수 단위로 분석한다는 가정 아래의 정의. 범용 분석기엔 그대로 안 맞지만, 편의상 이렇게 정한다."
$cap.TextFrame2.TextRange.Font.Name = "Aptos"
$cap.TextFrame2.TextRange.Font.NameFarEast = "맑은 고딕"
$cap.TextFrame2.TextRange.Font.Size = 11
$cap.TextFrame2.TextRange.Font.Fill.ForeColor.RGB = $Faint
$cap.TextFrame2.TextRange.ParagraphFormat.Alignment = 2   # center
$cap.TextFrame2.MarginLeft = 0; $cap.TextFrame2.MarginRight = 0
$cap.AlternativeText = "poster_insert:formula_caption"

# ---------- save & close ----------
$deck.Save()
$deck.Close()
$ppt.Quit()
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($slide) | Out-Null
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($deck)  | Out-Null
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($ppt)   | Out-Null
[System.GC]::Collect(); [System.GC]::WaitForPendingFinalizers()

Write-Host "done." -ForegroundColor Cyan
