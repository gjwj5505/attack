# insert_native_s3.ps1
# Replaces the two §03 image inserts (formula + nondet diagram) with
# fully-native PowerPoint elements (text boxes with Cambria Math, rounded
# rectangles, ovals, connector lines). Leaves everything else alone.

$ErrorActionPreference = 'Stop'
$here     = Split-Path -Parent $MyInvocation.MyCommand.Path
$pptxPath = Join-Path $here 'SigPL_new.pptx'

# ---------- palette ----------
function RGB([int]$r, [int]$g, [int]$b) { return $r + (256 * $g) + (65536 * $b) }
$Deep   = RGB 0   57  127
$Mid    = RGB 58  114 184
$Light  = RGB 169 198 230
$Lav    = RGB 214 222 235
$Mist   = RGB 239 244 248
$Rule   = RGB 195 207 222
$Ink    = RGB 26  34  43
$Body   = RGB 62  74  87
$Faint  = RGB 124 138 153
$Red    = RGB 210 60  60

$SANS = "Aptos"

# ---------- helpers (match build_body_v2 style) ----------
function New-Box($Sl, [double]$X, [double]$Y, [double]$W, [double]$H,
                 [int]$Fill = -1, [int]$Stroke = -1, [double]$Weight = 1) {
  $s = $Sl.Shapes.AddShape(1, $X, $Y, $W, $H)
  if ($Fill -lt 0) { $s.Fill.Visible = 0 } else { $s.Fill.Solid(); $s.Fill.ForeColor.RGB = $Fill }
  if ($Stroke -lt 0) { $s.Line.Visible = 0 }
  else { $s.Line.Visible = -1; $s.Line.ForeColor.RGB = $Stroke; $s.Line.Weight = $Weight }
  return $s
}
function New-RBox($Sl, [double]$X, [double]$Y, [double]$W, [double]$H,
                  [int]$Fill = -1, [int]$Stroke = -1, [double]$Weight = 1.0, [double]$R = 8) {
  $s = $Sl.Shapes.AddShape(5, $X, $Y, $W, $H)
  $adj = $R / [Math]::Min($W, $H); if ($adj -gt 0.5) { $adj = 0.5 }
  $s.Adjustments.Item(1) = $adj
  if ($Fill -lt 0) { $s.Fill.Visible = 0 } else { $s.Fill.Solid(); $s.Fill.ForeColor.RGB = $Fill }
  if ($Stroke -lt 0) { $s.Line.Visible = 0 }
  else { $s.Line.Visible = -1; $s.Line.ForeColor.RGB = $Stroke; $s.Line.Weight = $Weight }
  return $s
}
function New-Oval($Sl, [double]$X, [double]$Y, [double]$W, [double]$H, [int]$Fill) {
  $s = $Sl.Shapes.AddShape(9, $X, $Y, $W, $H)
  $s.Fill.Solid(); $s.Fill.ForeColor.RGB = $Fill
  $s.Line.Visible = 0
  return $s
}
function New-Line($Sl, [double]$X1, [double]$Y1, [double]$X2, [double]$Y2,
                  [int]$Color, [double]$Weight = 1.0) {
  $l = $Sl.Shapes.AddLine($X1, $Y1, $X2, $Y2)
  $l.Line.ForeColor.RGB = $Color; $l.Line.Weight = $Weight
  return $l
}
function New-Text($Sl, [string]$Text, [double]$X, [double]$Y, [double]$W, [double]$H,
                  [double]$Size, [int]$Color,
                  [string]$Font = "Aptos", [switch]$Bold, [int]$Align = 1, [int]$VAlign = 1) {
  $s = $Sl.Shapes.AddTextbox(1, $X, $Y, $W, $H)
  $tf = $s.TextFrame2
  $tf.AutoSize = 0; $tf.WordWrap = -1
  $tf.MarginLeft = 0; $tf.MarginRight = 0; $tf.MarginTop = 0; $tf.MarginBottom = 0
  $tf.VerticalAnchor = $VAlign
  $tf.TextRange.Text = $Text
  $tr = $tf.TextRange
  $tr.Font.Name = $Font
  $tr.Font.NameFarEast = "맑은 고딕"
  $tr.Font.Size = $Size
  $tr.Font.Bold = if ($Bold) { -1 } else { 0 }
  $tr.Font.Fill.ForeColor.RGB = $Color
  $tr.ParagraphFormat.Alignment = $Align
  $s.Left = $X; $s.Top = $Y; $s.Width = $W; $s.Height = $H
  return $s
}
function Set-MathGlyph($Shape, [string]$Text, [char]$Ch, [double]$Size) {
  $i = $Text.IndexOf($Ch); if ($i -lt 0) { return }
  $c = $Shape.TextFrame2.TextRange.Characters($i + 1, 1)
  $c.Font.Name = "Cambria Math"
  $c.Font.NameFarEast = "Cambria Math"
  $c.Font.Size = $Size
}
function Has-Text($sh) { try { return ([int]$sh.HasTextFrame -eq -1) } catch { return $false } }
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

# ---------- delete the image inserts we're replacing + their red notes ----------
Write-Host "removing old §03 inserts..." -ForegroundColor Cyan
$altsToKill = @(
  'poster_insert:attack_formula.png',
  'poster_insert:nondet_attack_body.png',
  'poster_insert:c_nondet_body.png',
  'poster_insert:formula_caption'
)
$noteMarkers = @('이거 ppt 수식으로', '여기 그림 ppt로')

$doomed = @()
foreach ($sh in $slide.Shapes) {
  $alt = ''; try { $alt = $sh.AlternativeText } catch {}
  if ($alt -and ($altsToKill -contains $alt)) { $doomed += @{ id=$sh.Id; hint="alt=$alt" }; continue }
  if (Has-Text $sh) {
    $t = Get-Text $sh
    foreach ($m in $noteMarkers) {
      if ($t -and $t.IndexOf($m) -ge 0) { $doomed += @{ id=$sh.Id; hint=$m }; break }
    }
  }
}
foreach ($d in $doomed) {
  foreach ($sh in $slide.Shapes) {
    if ($sh.Id -eq $d.id) {
      Write-Host ("  deleted: {0}" -f $d.hint) -ForegroundColor DarkGray
      $sh.Delete(); break
    }
  }
}

# ====================================================================
# NATIVE FORMULA — §03
# ====================================================================
Write-Host "inserting §03 formula (native, Cambria Math)..." -ForegroundColor Cyan
$fx = 74; $fy = 1140; $fw = 741
$formula = "∃ 지점 ℓ,   ∃ 변수 x.       C(ℓ)(x)  ⊄  A(ℓ)(x)       →   공격 성공"
$fs = New-Text $slide $formula $fx $fy $fw 40 22 $Deep -Bold -Align 2 -VAlign 3
$fs.AlternativeText = "poster_insert:formula_native"
# math glyphs (∃ = U+2203, ⊄ = U+2284, → = U+2192)
Set-MathGlyph $fs $formula ([char]0x2203) 24
Set-MathGlyph $fs $formula ([char]0x2203) 24   # both ∃
# handle the second ∃ (both occurrences)
$tr = $fs.TextFrame2.TextRange
foreach ($m in [regex]::Matches($formula, [regex]::Escape([char]0x2203))) {
  $c = $tr.Characters($m.Index + 1, 1)
  $c.Font.Name = "Cambria Math"; $c.Font.NameFarEast = "Cambria Math"; $c.Font.Size = 24
}
# ⊄ (U+2284)
foreach ($m in [regex]::Matches($formula, [regex]::Escape([char]0x2284))) {
  $c = $tr.Characters($m.Index + 1, 1)
  $c.Font.Name = "Cambria Math"; $c.Font.NameFarEast = "Cambria Math"; $c.Font.Size = 26
}
# italicize ℓ and x variables
foreach ($ch in @([char]0x2113, 'x')) {
  foreach ($m in [regex]::Matches($formula, [regex]::Escape([string]$ch))) {
    $c = $tr.Characters($m.Index + 1, 1)
    $c.Font.Italic = -1
    $c.Font.Name = "Cambria Math"; $c.Font.NameFarEast = "Cambria Math"
  }
}

# caption below
$cap = New-Text $slide "분석기가 위치·변수 단위로 분석한다는 가정 아래의 정의. 범용 분석기엔 그대로 안 맞지만, 편의상 이렇게 정한다." $fx 1185 $fw 24 12 $Faint -Align 2
$cap.AlternativeText = "poster_insert:formula_caption_native"

# ====================================================================
# NATIVE NONDET DIAGRAM — §03
# ====================================================================
Write-Host "inserting §03 nondet diagram (native shapes)..." -ForegroundColor Cyan

# outer light card that contains both rows
$dcX = 74; $dcY = 1370; $dcW = 741; $dcH = 165
$card = New-RBox $slide $dcX $dcY $dcW $dcH $Mist $Rule 1.0 -R 12
$card.AlternativeText = "poster_insert:nondet_card"

# ------- Row 1: 공격 성공 (겉보기) -------
$r1y = $dcY + 12
[void](New-Text $slide "공격을 성공했다고 생각했는데…" ($dcX + 20) $r1y 380 20 13 $Ink -Bold -Align 1)
# abstract box (empty)
$absX = $dcX + 240; $absY = $r1y + 8
[void](New-RBox $slide $absX $absY 82 46 $Lav $Mid 1 -R 6)
[void](New-Text $slide "abstract" $absX $absY 82 20 10 $Mid -Align 2)
# concrete dot outside
$cX = $absX + 130
[void](New-Oval $slide $cX ($absY + 20) 8 8 $Red)
[void](New-Text $slide "concrete" ($cX - 22) ($absY + 32) 52 14 9 $Faint -Align 2)
# conclusion arrow text
[void](New-Text $slide "⇒  soundness 깨짐 (공격 성공?)" ($cX + 30) ($absY + 15) 280 20 12 $Ink -Align 1)

# ------- Row 2: 사실은 비결정성 때문 -------
$r2y = $dcY + 80
[void](New-Text $slide "사실 그건 비결정성 때문이었다고?!" ($dcX + 20) $r2y 380 20 13 $Ink -Bold -Align 1)
$absX2 = $dcX + 240; $absY2 = $r2y + 8
[void](New-RBox $slide $absX2 $absY2 82 46 $Lav $Mid 1 -R 6)
# concrete dot INSIDE abstract (labeled Sparrow-concrete)
[void](New-Oval $slide ($absX2 + 30) ($absY2 + 18) 8 8 $Red)
[void](New-Text $slide "Sparrow-concrete" ($absX2 - 18) ($absY2 + 48) 120 14 8 $Faint -Align 2)
# concrete dot OUTSIDE (Attack-concrete)
$cX2 = $absX2 + 130
[void](New-Oval $slide $cX2 ($absY2 + 20) 8 8 $Red)
[void](New-Text $slide "Attack-concrete" ($cX2 - 24) ($absY2 + 48) 60 14 8 $Faint -Align 2)
[void](New-Text $slide "⇒  soundness 안 깨짐" ($cX2 + 30) ($absY2 + 15) 280 20 12 $Ink -Align 1)

# ---------- save & close ----------
$deck.Save()
$deck.Close()
$ppt.Quit()
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($slide) | Out-Null
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($deck)  | Out-Null
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($ppt)   | Out-Null
[System.GC]::Collect(); [System.GC]::WaitForPendingFinalizers()

Write-Host "done." -ForegroundColor Cyan
