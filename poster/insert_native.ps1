# insert_native.ps1
# Adds the prepared content into SigPL_new.pptx using PowerPoint's native
# shapes (text boxes, lines, rectangles, ovals, tables) instead of raster
# images. Everything stays editable inside PowerPoint.
#
# Anchors are the red-text placeholder markers the user left in the slide.
# Only ADDs content; does not delete anything, so the user can freely
# rearrange or trim.

$ErrorActionPreference = 'Stop'

$here     = Split-Path -Parent $MyInvocation.MyCommand.Path
$pptxPath = Join-Path $here 'SigPL_new.pptx'

# ---------- palette (matches build_body_v2.ps1) ----------
function RGB([int]$r, [int]$g, [int]$b) { return $r + (256 * $g) + (65536 * $b) }
$Deep   = RGB 0 57 127
$Mid    = RGB 58 114 184
$Light  = RGB 169 198 230
$Lav    = RGB 214 222 235
$Mist   = RGB 239 244 248
$Rule   = RGB 195 207 222
$Ink    = RGB 26 34 43
$Body   = RGB 62 74 87
$Faint  = RGB 124 138 153
$Paper  = RGB 255 255 255
$Dark   = RGB 46 52 64
$OnDark = RGB 216 222 233
$Match  = RGB 215 110 55
$Red    = RGB 200 40 40

$SANS = "Aptos"
$MONO = "Consolas"

# ---------- shape / text helpers ----------
function New-Box($Sl, [double]$X, [double]$Y, [double]$W, [double]$H,
                 [int]$Fill = -1, [int]$Stroke = -1, [double]$Weight = 1) {
  $s = $Sl.Shapes.AddShape(1, $X, $Y, $W, $H)
  if ($Fill -lt 0) { $s.Fill.Visible = 0 } else { $s.Fill.Solid(); $s.Fill.ForeColor.RGB = $Fill }
  if ($Stroke -lt 0) { $s.Line.Visible = 0 }
  else { $s.Line.Visible = -1; $s.Line.ForeColor.RGB = $Stroke; $s.Line.Weight = $Weight }
  return $s
}
function New-RBox($Sl, [double]$X, [double]$Y, [double]$W, [double]$H,
                  [int]$Fill = -1, [int]$Stroke = -1, [double]$Weight = 1.2, [double]$R = 8) {
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
                  [int]$Color, [double]$Weight = 1.0, [switch]$Arrow) {
  $l = $Sl.Shapes.AddLine($X1, $Y1, $X2, $Y2)
  $l.Line.ForeColor.RGB = $Color; $l.Line.Weight = $Weight
  if ($Arrow) { $l.Line.EndArrowheadStyle = 3; $l.Line.EndArrowheadLength = 2; $l.Line.EndArrowheadWidth = 2 }
  return $l
}
function New-Text($Sl, [string]$Text, [double]$X, [double]$Y, [double]$W, [double]$H,
                  [double]$Size, [int]$Color,
                  [string]$Font = "Aptos", [switch]$Bold, [int]$Align = 1, [int]$VAlign = 1,
                  [double]$Space = 1.0) {
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
  $tr.ParagraphFormat.SpaceWithin = $Space
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

# ---------- proof-tree building blocks ----------
# Draw a monospace line and (optionally) a rule line above it. Returns the
# text box shape so callers can measure its width.
function Judg($Sl, [string]$Text, [double]$X, [double]$Y, [double]$Size = 12,
              [switch]$RuleBefore, [double]$RuleExtend = 6, [int]$RuleColor = -1) {
  if ($RuleBefore) {
    $rc = $RuleColor; if ($rc -lt 0) { $rc = $script:Ink }
    # measured width guess: assume ~7pt per char for Consolas at 12pt
    # user will fine-tune, so we just draw a generous line
    $tw = $Text.Length * ($Size * 0.55)
    New-Line $Sl ($X - $RuleExtend) ($Y - 3) ($X + $tw + $RuleExtend) ($Y - 3) $rc 0.75 | Out-Null
  }
  $t = New-Text $Sl $Text $X $Y ($Text.Length * ($Size * 0.55) + 20) ($Size * 1.5) $Size $script:Ink -Font $script:MONO -Align 1
  return $t
}

# Draw a horizontal rule of specific span between two X coordinates
function Rule($Sl, [double]$X1, [double]$X2, [double]$Y, [int]$Color = -1, [double]$Weight = 0.75) {
  $c = $Color; if ($c -lt 0) { $c = $script:Ink }
  New-Line $Sl $X1 $Y $X2 $Y $c $Weight | Out-Null
}

# ---------- open PPT ----------
Write-Host "opening PowerPoint..." -ForegroundColor Cyan
$ppt = New-Object -ComObject PowerPoint.Application
$ppt.Visible = [Microsoft.Office.Core.MsoTriState]::msoTrue
$deck = $ppt.Presentations.Open($pptxPath, $false, $false, $true)
$slide = $deck.Slides.Item(1)

# ====================================================================
# §01 attack example (anchor: marker [87] at L=297 T=818 W=285 H=29)
# ====================================================================
Write-Host "  §01 attack example..." -ForegroundColor Green
# code block
$codeX = 150; $codeY = 862; $codeW = 380
[void](New-RBox $slide $codeX $codeY $codeW 138 $Dark -R 8)
$code01 = "if x > 0:`n    x = 3`nelse:`n    x = -3`ny = 10 / x"
$c01 = New-Text $slide $code01 ($codeX + 20) ($codeY + 14) ($codeW - 40) 110 15 $OnDark -Font $MONO -Space 1.2
# colour the false-alarm line's `y = 10 / x`
$last = $code01.IndexOf("y = 10 / x") + 1
$c01.TextFrame2.TextRange.Characters($last, 10).Font.Fill.ForeColor.RGB = $Red
# caption
[void](New-Text $slide "→ false alarm 발생 (x가 실제로 0이 아닌데 분석기는 0을 포함한다고 잡음)" $codeX ($codeY + 148) $codeW 20 12 $Faint)

# number line (concrete points -3, 3 as red dots; abstract interval [-3, 3] as blue brackets)
$nlX = 140.0; $nlY = 1030.0; $nlW = 400.0
$step = $nlW / 10.0
[void](New-Line $slide $nlX ($nlY + 16) ($nlX + $nlW) ($nlY + 16) $Ink 1.0 -Arrow)
for ($v = -5; $v -le 5; $v++) {
  $xv = $nlX + ($v + 5) * $step
  [void](New-Line $slide $xv ($nlY + 12) $xv ($nlY + 20) $Ink 0.75)
  [void](New-Text $slide ([string]$v) ($xv - 8) ($nlY + 22) 16 14 8 $Ink -Font $MONO -Align 2)
}
# blue interval brackets at -3 and 3
$xm3 = $nlX + (-3 + 5) * $step
$xp3 = $nlX + ( 3 + 5) * $step
[void](New-Line $slide $xm3 ($nlY + 6)  ($xm3 - 4) ($nlY + 6)  $Mid 1.5)
[void](New-Line $slide $xm3 ($nlY + 6)  $xm3       ($nlY + 26) $Mid 1.5)
[void](New-Line $slide $xm3 ($nlY + 26) ($xm3 - 4) ($nlY + 26) $Mid 1.5)
[void](New-Line $slide $xp3 ($nlY + 6)  ($xp3 + 4) ($nlY + 6)  $Mid 1.5)
[void](New-Line $slide $xp3 ($nlY + 6)  $xp3       ($nlY + 26) $Mid 1.5)
[void](New-Line $slide $xp3 ($nlY + 26) ($xp3 + 4) ($nlY + 26) $Mid 1.5)
[void](New-Text $slide "[−3, 3]" ($xm3 - 6) ($nlY - 14) 60 16 11 $Mid -Bold -Align 1 -Font $MONO)
# red concrete dots at -3, 3
foreach ($v in @(-3, 3)) {
  $xv = $nlX + ($v + 5) * $step
  [void](New-Oval $slide ($xv - 3) ($nlY + 13) 6 6 $Red)
}
# red "0 with circle" — small ring at 0
$x0 = $nlX + (0 + 5) * $step
[void](New-Oval $slide ($x0 - 4) ($nlY + 12) 8 8 $Red)
[void](New-Oval $slide ($x0 - 2) ($nlY + 14) 4 4 $Paper)
[void](New-Text $slide "이 0이 분석기가 잘못 포함한 값" ($nlX + 90) ($nlY + 48) 260 20 11 $Red -Align 1)

# ====================================================================
# §03 nondet diagrams (anchor: marker [89] L=132 T=1403 W=655 H=73)
# ====================================================================
Write-Host "  §03 nondet diagrams..." -ForegroundColor Green
$ndX = 90; $ndY = 1478
# ---- Row 1: 공격 성공 (겉보기)
[void](New-Text $slide "공격을 성공했다고 생각했는데…" $ndX $ndY 380 20 12 $Ink -Bold)
# abstract box + concrete dot + arrow text
[void](New-RBox $slide ($ndX + 10) ($ndY + 26) 90 60 $Lav $Mid 1 -R 5)
[void](New-Text $slide "abstract" ($ndX + 10) ($ndY + 40) 90 20 10 $Mid -Align 2)
[void](New-Oval $slide ($ndX + 150) ($ndY + 52) 8 8 $Red)
[void](New-Text $slide "concrete" ($ndX + 130) ($ndY + 64) 60 14 9 $Faint -Align 2)
[void](New-Text $slide "⇒ soundness 깨짐 (공격 성공!)" ($ndX + 180) ($ndY + 48) 260 20 12 $Ink)

# ---- Row 2: 사실은 비결정성 때문
$ndY2 = $ndY + 108
[void](New-Text $slide "사실 그건 비결정성 때문이었다고?!" $ndX $ndY2 380 20 12 $Ink -Bold)
[void](New-RBox $slide ($ndX + 10) ($ndY2 + 26) 90 60 $Lav $Mid 1 -R 5)
[void](New-Text $slide "abstract" ($ndX + 10) ($ndY2 + 34) 90 20 10 $Mid -Align 2)
[void](New-Oval $slide ($ndX + 50) ($ndY2 + 52) 8 8 $Red)
[void](New-Text $slide "Sparrow-concrete" ($ndX + 5) ($ndY2 + 88) 110 14 9 $Faint -Align 2)
[void](New-Oval $slide ($ndX + 150) ($ndY2 + 52) 8 8 $Red)
[void](New-Text $slide "Attack-concrete" ($ndX + 125) ($ndY2 + 88) 100 14 9 $Faint -Align 2)
[void](New-Text $slide "⇒ soundness 깨지지 않음" ($ndX + 240) ($ndY2 + 48) 260 20 12 $Ink)

[void](New-Text $slide "따라서 모든 비결정성을 제거해야 올바른 공격 — 그래서 CIL− (비결정성 제거된 C 스타일 작은 언어)" $ndX ($ndY2 + 120) 700 24 12 $Deep -Bold)

# ---- C nondet table (below the diagrams)
Write-Host "  §03 C nondet table..." -ForegroundColor Green
$tX = 90; $tY = $ndY2 + 158; $tW = 700; $tH = 190
$tbl = $slide.Shapes.AddTable(9, 4, $tX, $tY, $tW, $tH)
$tbl.Table.Columns.Item(1).Width = 160
$tbl.Table.Columns.Item(2).Width = 200
$tbl.Table.Columns.Item(3).Width = 190
$tbl.Table.Columns.Item(4).Width = 150

$rows = @(
  @('예', 'C', 'CIL', 'CIL−'),
  @('h(f(),g()) f()+g() {f(),g()}', '계산 순서 비결정', '함수 호출은 expression으로 X', 'OK'),
  @('sizeof(int (*)[n++])', 'n++을 실행하거나/않거나', 'n++ 문법 없음', 'OK'),
  @('i = i++ + 1;', 'Undefined Behavior', 'i++ 문법 없음', 'OK'),
  @('int x; use(x);', 'indeterminate value', 'indeterminate value', '합성 시 생성 X'),
  @('"a" == "a"', 'true/false 모두 가능', '여전히 비결정적', 'string 없음'),
  @('char c = -1;', '-1 / 255', '여전히 비결정적', 'char 없음'),
  @('x >> 1', 'x < 0일 때 UB', '여전히 비결정적', '비트연산 없음'),
  @('malloc(n)', '메모리 주소 비결정', 'fresh object', '포인터 없음')
)
for ($r = 0; $r -lt 9; $r++) {
  for ($c = 0; $c -lt 4; $c++) {
    $cell = $tbl.Table.Cell($r + 1, $c + 1)
    $cell.Shape.TextFrame2.TextRange.Text = $rows[$r][$c]
    $tr = $cell.Shape.TextFrame2.TextRange
    if ($r -eq 0) { $tr.Font.Bold = -1; $tr.Font.Size = 11; $tr.Font.Fill.ForeColor.RGB = $Deep }
    else { $tr.Font.Size = 10; $tr.Font.Fill.ForeColor.RGB = $Ink }
    $tr.Font.NameFarEast = "맑은 고딕"
    if ($c -eq 0) { $tr.Font.Name = $MONO } else { $tr.Font.Name = $SANS }
    $cell.Shape.TextFrame2.MarginLeft = 4; $cell.Shape.TextFrame2.MarginRight = 4
    $cell.Shape.TextFrame2.MarginTop = 2;  $cell.Shape.TextFrame2.MarginBottom = 2
  }
}

# ====================================================================
# §03 공격의 정의 — formula (below marker [90] L=137 T=1146)
# ====================================================================
Write-Host "  §03 formula..." -ForegroundColor Green
$fx = 90; $fy = 1246
$formula = "∃ 지점 ℓ,  ∃ 변수 x.    C(ℓ)(x)  ⊄  A(ℓ)(x)     → 공격 성공"
$fs = New-Text $slide $formula $fx $fy 700 30 18 $Deep -Bold -Align 2
Set-MathGlyph $fs $formula ([char]0x2203) 20
Set-MathGlyph $fs $formula ([char]0x2284) 22
[void](New-Text $slide "분석기가 위치·변수 단위로 분석한다는 가정 아래의 정의. 범용 분석기엔 그대로 안 맞지만, 편의상 이렇게 정한다." $fx ($fy + 30) 700 30 11 $Faint -Align 2)

# ====================================================================
# §04 merge_trees (anchor: marker [82] L=1310 T=1367 W=304 H=29)
# ====================================================================
Write-Host "  §04 merged proof tree..." -ForegroundColor Green
$mtX = 869; $mtY = 1411
# labels
[void](New-Text $slide "증명나무 A" $mtX ($mtY + 5) 200 18 12 $Deep -Bold)
[void](New-Text $slide "증명나무 B" ($mtX + 250) ($mtY + 5) 200 18 12 $Deep -Bold)
# Tree A: top axiom line
[void](New-Text $slide "{} ⊢ 1 ⇒ 1" $mtX ($mtY + 26) 160 18 12 $Ink -Font $MONO)
Rule $slide $mtX ($mtX + 130) ($mtY + 44)
# Tree A: bottom (conclusion)
$aBot = New-Text $slide "{} ⊢ x := 1; ⇒ {x: 1}" $mtX ($mtY + 46) 200 18 12 $Ink -Font $MONO
# Highlight box on {x: 1}
[void](New-RBox $slide ($mtX + 118) ($mtY + 45) 44 20 -1 $Match 1.2 -R 3)

# Tree B: top axioms (two side by side)
[void](New-Text $slide "{x:1} ⊢ x ⇒ 1" ($mtX + 250) ($mtY + 26) 130 18 12 $Ink -Font $MONO)
[void](New-Text $slide "{x:1} ⊢ 2 ⇒ 2" ($mtX + 390) ($mtY + 26) 130 18 12 $Ink -Font $MONO)
Rule $slide ($mtX + 250) ($mtX + 500) ($mtY + 44)
# Tree B: middle
[void](New-Text $slide "{x:1} ⊢ x + 2 ⇒ 3" ($mtX + 310) ($mtY + 46) 180 18 12 $Ink -Font $MONO)
Rule $slide ($mtX + 250) ($mtX + 500) ($mtY + 64)
# Tree B: bottom (conclusion) — highlight the leading {x:1}
[void](New-Text $slide "{x:1} ⊢ y := x + 2; ⇒ {x:1, y:3}" ($mtX + 250) ($mtY + 66) 300 18 12 $Ink -Font $MONO)
[void](New-RBox $slide ($mtX + 248) ($mtY + 65) 40 20 -1 $Match 1.2 -R 3)

# Merged tree (bottom row)
$mgY = $mtY + 130
[void](New-Text $slide "{} ⊢ x := 1; ⇒ {x:1}" $mtX ($mgY) 200 18 12 $Ink -Font $MONO)
[void](New-RBox $slide ($mtX + 115) ($mgY - 1) 44 20 -1 $Match 1.2 -R 3)
[void](New-Text $slide "{x:1} ⊢ y := x + 2; ⇒ {x:1, y:3}" ($mtX + 250) ($mgY) 300 18 12 $Ink -Font $MONO)
[void](New-RBox $slide ($mtX + 248) ($mgY - 1) 40 20 -1 $Match 1.2 -R 3)
Rule $slide $mtX ($mtX + 570) ($mgY + 20)
[void](New-Text $slide "{} ⊢ x := 1; y := x + 2; ⇒ {x:1, y:3}" $mtX ($mgY + 22) 570 18 12 $Ink -Font $MONO -Align 2)
[void](New-Text $slide "합쳐진 증명나무" $mtX ($mgY + 46) 570 18 12 $Deep -Bold -Align 2)

# Connecting arrows (A -> merged left, B -> merged right)
[void](New-Line $slide ($mtX + 140) ($mtY + 68) ($mtX + 140) ($mgY - 2) $Faint 1.2 -Arrow)
[void](New-Line $slide ($mtX + 270) ($mtY + 88) ($mtX + 270) ($mgY - 2) $Faint 1.2 -Arrow)

# Side caption
[void](New-Text $slide "연결점 메모리 일치" ($mtX + 590) ($mgY - 10) 200 20 11 $Match -Bold)
[void](New-Text $slide "A의 결과 메모리 = B의 시작 메모리 ({x:1})가 같아야 Seq 규칙으로 이을 수 있다." ($mtX + 590) ($mgY + 10) 180 60 10 $Faint)

# ====================================================================
# §05 size_semantics_big (anchor: marker [92] L=58 T=1771)
# ====================================================================
Write-Host "  §05 semantics-big proof tree..." -ForegroundColor Green
$s1X = 74; $s1Y = 1815
[void](New-Text $slide "코드는 짧지만 증명나무는 100단 —" $s1X $s1Y 380 18 11 $Deep -Bold)
$px = $s1X + 20; $py = $s1Y + 24
[void](New-Text $slide "{x:100} ⊢ (x<100) ⇒ 0" $px $py 300 16 10.5 $Ink -Font $MONO)
Rule $slide $px ($px + 240) ($py + 18)
[void](New-Text $slide "{x:100} ⊢ while (x<100) x:=x+1 ⇒ {x:100}" $px ($py + 20) 320 16 10.5 $Ink -Font $MONO)
[void](New-Text $slide "⋮" ($px + 130) ($py + 42) 40 20 12 $Ink -Font $MONO -Align 2)
[void](New-Text $slide "(≈100단 반복)" ($px + 200) ($py + 42) 140 20 10 $Match -Bold)
[void](New-Text $slide "{x:0} ⊢ (x<100) ⇒ 1    {x:0} ⊢ x:=x+1 ⇒ {x:1}    {x:1} ⊢ while … ⇒ {x:100}" $px ($py + 70) 480 16 9.5 $Ink -Font $MONO)
Rule $slide $px ($px + 470) ($py + 88)
[void](New-Text $slide "{x:0} ⊢ while (x<100) x:=x+1 ⇒ {x:100}" $px ($py + 90) 400 16 10.5 $Ink -Font $MONO)
[void](New-Text $slide "{} ⊢ x:=0 ⇒ {x:0}      {x:0} ⊢ while (x<100) x:=x+1 ⇒ {x:100}" $px ($py + 112) 500 16 10.5 $Ink -Font $MONO)
Rule $slide $px ($px + 470) ($py + 130)
[void](New-Text $slide "{} ⊢ x:=0; while (x<100) x:=x+1 ⇒ {x:100}" $px ($py + 132) 470 16 10.5 $Ink -Font $MONO)

# ====================================================================
# §05 size_prog_big (anchor: marker [91] L=458 T=1771)
# ====================================================================
Write-Host "  §05 program-big proof tree..." -ForegroundColor Green
$s2X = 474; $s2Y = 1815
[void](New-Text $slide "코드는 길지만 증명나무는 자명 (while 조건이 처음부터 거짓)" $s2X $s2Y 380 18 11 $Deep -Bold)
$px2 = $s2X + 20; $py2 = $s2Y + 24
[void](New-Text $slide "{x:1} ⊢ (x<1) ⇒ 0" $px2 $py2 260 16 10.5 $Ink -Font $MONO)
Rule $slide $px2 ($px2 + 260) ($py2 + 18)
$whileBody = "{x:1} ⊢ while (x<1)  ⇒  {x:1}`n              x := (x+1);`n              x := (x+1);`n              x := (x+1);`n              x := (x+1)"
[void](New-Text $slide $whileBody $px2 ($py2 + 20) 340 96 10.5 $Ink -Font $MONO -Space 1.1)

# ====================================================================
# §06 unify_example (anchor: marker [83] L=1053 T=1961)
# ====================================================================
Write-Host "  §06 unification code panels..." -ForegroundColor Green
$uY = 2010
$panelW = 200
# Panel A
[void](New-Text $slide "// A" 90 $uY 100 16 10 $Faint -Font $MONO)
$codeA = "if (x > 0 && ??) {`n  return 0;`n}`n??"
[void](New-Text $slide $codeA 90 ($uY + 18) $panelW 90 11 $Ink -Font $MONO -Space 1.2)
# op ⊔
[void](New-Text $slide "⊔" (90 + $panelW + 10) ($uY + 44) 30 24 20 $Faint -Bold -Align 2)
# Panel B
$bx = 90 + $panelW + 50
[void](New-Text $slide "// B" $bx $uY 100 16 10 $Faint -Font $MONO)
$codeB = "if (?? && ??) {`n  ??`n}`nx = 1;"
[void](New-Text $slide $codeB $bx ($uY + 18) $panelW 90 11 $Ink -Font $MONO -Space 1.2)
# op =
[void](New-Text $slide "=" ($bx + $panelW + 10) ($uY + 44) 30 24 20 $Faint -Bold -Align 2)
# Panel A ⊔ B
$ux = $bx + $panelW + 50
$ulabel = "// A ⊔ B  (unify 결과)"
[void](New-Text $slide $ulabel $ux $uY 200 16 10 $Faint -Font $MONO)
$codeU = "if (x > 0 && ??) {`n  return 0;`n}`nx = 1;"
[void](New-Text $slide $codeU $ux ($uY + 18) $panelW 90 11 $Ink -Font $MONO -Space 1.2)

# ---------- save & close ----------
$deck.Save()
$deck.Close()
$ppt.Quit()
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($slide) | Out-Null
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($deck)  | Out-Null
[System.Runtime.InteropServices.Marshal]::ReleaseComObject($ppt)   | Out-Null
[System.GC]::Collect(); [System.GC]::WaitForPendingFinalizers()

Write-Host "done." -ForegroundColor Cyan
