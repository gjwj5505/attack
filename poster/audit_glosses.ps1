# audit_glosses.ps1
# Scans every text run in the slide, groups characters by (size, color, bold),
# and reports runs whose size is markedly smaller than surrounding text — those
# are the English gloss annotations. Flags size/color inconsistencies.

$ErrorActionPreference = 'Stop'
$here     = Split-Path -Parent $MyInvocation.MyCommand.Path
$pptxPath = Join-Path $here 'SigPL_new.pptx'
$outPath  = Join-Path $here 'gloss_audit.txt'

$ppt = New-Object -ComObject PowerPoint.Application
$deck = $ppt.Presentations.Open($pptxPath, $true, $false, $false)
$slide = $deck.Slides.Item(1)

$out = New-Object System.Collections.Generic.List[string]

$shapeIdx = 0
foreach ($sh in $slide.Shapes) {
  $shapeIdx++
  try { if ([int]$sh.HasTextFrame -ne -1) { continue } } catch { continue }
  $tr = $null
  try { $tr = $sh.TextFrame2.TextRange } catch { continue }
  if ($null -eq $tr -or $tr.Length -eq 0) { continue }

  $full = $tr.Text
  # walk character by character and group consecutive chars with same (size, color, bold)
  $groups = @()
  $curSize = -1; $curColor = -1; $curBold = -1
  $curText = ''
  for ($i = 1; $i -le $tr.Length; $i++) {
    $ch = $tr.Characters($i, 1)
    $sz = [double]$ch.Font.Size
    $co = -1
    try { $co = [int]$ch.Font.Fill.ForeColor.RGB } catch { $co = -1 }
    $bo = -1
    try { $bo = [int]$ch.Font.Bold } catch {}
    $c  = $ch.Text
    if ($sz -ne $curSize -or $co -ne $curColor -or $bo -ne $curBold) {
      if ($curText.Length -gt 0) {
        $groups += @{ text=$curText; size=$curSize; color=$curColor; bold=$curBold }
      }
      $curSize = $sz; $curColor = $co; $curBold = $bo; $curText = $c
    } else {
      $curText += $c
    }
  }
  if ($curText.Length -gt 0) {
    $groups += @{ text=$curText; size=$curSize; color=$curColor; bold=$curBold }
  }
  # find the max size in this shape — that's the "parent size"
  $maxSize = 0
  foreach ($g in $groups) { if ($g.size -gt $maxSize) { $maxSize = $g.size } }
  # emit groups whose size < 0.85 * maxSize AND text contains ASCII letters
  foreach ($g in $groups) {
    $isSmaller = ($maxSize -gt 0 -and $g.size / $maxSize -lt 0.85)
    $hasAscii  = ($g.text -match '[A-Za-z]')
    if ($isSmaller -and $hasAscii) {
      $ratio = [Math]::Round($g.size / $maxSize, 3)
      $rgb   = "#{0:X6}" -f $g.color
      $ttrim = $g.text -replace "`r","|" -replace "`n","|"
      if ($ttrim.Length -gt 30) { $ttrim = $ttrim.Substring(0, 30) + '…' }
      $out.Add(("[{0,3}] parent={1,5:F1}  gloss={2,5:F1}  ratio={3}  color={4}  bold={5}  '{6}'" -f `
                $shapeIdx, $maxSize, $g.size, $ratio, $rgb, $g.bold, $ttrim))
    }
  }
}

[System.IO.File]::WriteAllLines($outPath, $out, [System.Text.UTF8Encoding]::new($false))
$deck.Close(); $ppt.Quit()
Write-Host "wrote $outPath ($($out.Count) gloss runs)"
