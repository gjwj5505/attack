# fix_glosses.ps1
#
# Normalizes English-gloss annotations across the slide:
#   • Color unification — gloss runs whose color is currently Body (#3E4A57)
#     or plain gray #D9D9D9 are converted to the standard Faint (#7C8A99),
#     or to Light on dark parents.
#   • Size — gloss runs whose ratio-to-parent exceeds 0.72 are re-set to
#     0.68 × parent (matching build_body_v2's convention).
#   • Bold — any bold gloss run is set non-bold.
#
# Formula runs are skipped (identified by the Deep color used for the §03
# math formula).

$ErrorActionPreference = 'Stop'
$here     = Split-Path -Parent $MyInvocation.MyCommand.Path
$pptxPath = Join-Path $here 'SigPL_new.pptx'

# ---------- palette (COM ints) ----------
function RGB([int]$r, [int]$g, [int]$b) { return $r + (256 * $g) + (65536 * $b) }
$Faint   = RGB 124 138 153    # #7C8A99 → 0x998A7C
$Light   = RGB 169 198 230
$Body    = RGB 62  74  87
$Deep    = RGB 0   57  127

# gloss color threshold: parents lighter than this get Light glosses,
# otherwise Faint. luminance = 0.299R + 0.587G + 0.114B (Rec.601)
function Is-LightBg([int]$rgbCom) {
  $b = ($rgbCom -shr 16) -band 0xFF
  $g = ($rgbCom -shr 8)  -band 0xFF
  $r =  $rgbCom          -band 0xFF
  $lum = 0.299 * $r + 0.587 * $g + 0.114 * $b
  return ($lum -ge 180)
}

# ---------- open PPT ----------
Write-Host "opening PowerPoint..." -ForegroundColor Cyan
$ppt = New-Object -ComObject PowerPoint.Application
$ppt.Visible = [Microsoft.Office.Core.MsoTriState]::msoTrue
$deck = $ppt.Presentations.Open($pptxPath, $false, $false, $true)
$slide = $deck.Slides.Item(1)

$fixed = 0
$shapeIdx = 0
foreach ($sh in $slide.Shapes) {
  $shapeIdx++
  try { if ([int]$sh.HasTextFrame -ne -1) { continue } } catch { continue }
  $tr = $null
  try { $tr = $sh.TextFrame2.TextRange } catch { continue }
  if ($null -eq $tr -or $tr.Length -eq 0) { continue }

  # build character-run groups
  $groups = @()
  $curSize = -1; $curColor = -1; $curBold = -1; $curStart = 1; $curLen = 0; $curText = ''
  for ($i = 1; $i -le $tr.Length; $i++) {
    $ch = $tr.Characters($i, 1)
    $sz = [double]$ch.Font.Size
    $co = -1; try { $co = [int]$ch.Font.Fill.ForeColor.RGB } catch {}
    $bo = -1; try { $bo = [int]$ch.Font.Bold } catch {}
    $c  = $ch.Text
    if ($sz -ne $curSize -or $co -ne $curColor -or $bo -ne $curBold) {
      if ($curLen -gt 0) {
        $groups += @{ start=$curStart; length=$curLen; text=$curText; size=$curSize; color=$curColor; bold=$curBold }
      }
      $curSize = $sz; $curColor = $co; $curBold = $bo
      $curStart = $i; $curLen = 1; $curText = $c
    } else {
      $curLen++; $curText += $c
    }
  }
  if ($curLen -gt 0) {
    $groups += @{ start=$curStart; length=$curLen; text=$curText; size=$curSize; color=$curColor; bold=$curBold }
  }

  # find max size (the parent) and its color
  $maxSize = 0.0; $parentColor = -1
  foreach ($g in $groups) {
    if ($g.size -gt $maxSize) { $maxSize = $g.size; $parentColor = $g.color }
  }
  if ($maxSize -le 0) { continue }

  # target gloss color depends on parent brightness
  $targetGlossColor = if (Is-LightBg $parentColor) { $Light } else { $Faint }
  # target gloss size (only apply the 0.68 rule for body-scale parents 10..24pt)
  $applySize = ($maxSize -ge 10 -and $maxSize -le 24)
  $targetGlossSize = [double]([Math]::Round($maxSize * 0.68 * 2) / 2.0)

  foreach ($g in $groups) {
    $isSmaller = ($g.size / $maxSize -lt 0.85)
    $hasAscii  = ($g.text -match '[A-Za-z]')
    if (-not ($isSmaller -and $hasAscii)) { continue }

    # skip formula body ranges (parent color Deep AND text contains Korean)
    if ($parentColor -eq $Deep -and $g.text -match '[가-힣]') { continue }

    $range = $tr.Characters($g.start, $g.length)
    $changed = @()
    # color
    if ($g.color -ne $targetGlossColor) {
      $range.Font.Fill.ForeColor.RGB = $targetGlossColor
      $changed += "color"
    }
    # size
    if ($applySize -and [Math]::Abs($g.size - $targetGlossSize) -gt 0.1) {
      $range.Font.Size = $targetGlossSize
      $changed += "size $($g.size)→$targetGlossSize"
    }
    # bold off
    if ($g.bold -ne 0) {
      $range.Font.Bold = 0
      $changed += "unbold"
    }
    if ($changed.Count -gt 0) {
      $fixed++
      $t = $g.text
      if ($t.Length -gt 18) { $t = $t.Substring(0, 18) + '…' }
      Write-Host ("  [{0,3}] '{1,-20}' parent={2,4:F1}  {3}" -f $shapeIdx, $t, $maxSize, ($changed -join ', ')) -ForegroundColor DarkGray
    }
  }
}

Write-Host "fixed $fixed gloss runs" -ForegroundColor Green

$deck.Save()
$deck.Close()
$ppt.Quit()
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($slide) | Out-Null
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($deck)  | Out-Null
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($ppt)   | Out-Null
[System.GC]::Collect(); [System.GC]::WaitForPendingFinalizers()
Write-Host "done." -ForegroundColor Cyan
