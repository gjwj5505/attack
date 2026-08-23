# SIGPL 여름학교 2026 포스터 세션 — 내용은 그대로, 디자인만 assets/sample/POPL_new.pdf 계보로.
#
# 샘플에서 가져온 것: 전면 딥블루 헤더 + 거대한 흰 제목, 큰 파란 섹션 제목,
# 라벤더/미스트 라운드 패널, Nord 계열 어두운 코드 블록, 아래쪽 셰브론 장식과
# 로고 줄, 맨 아래 딥블루 밴드. 학회 표기는 POPL이 아니라 SIGPL.
#
# Usage:
#   powershell -ExecutionPolicy Bypass -File build_sigpl_poster_new.ps1 `
#     -PptxPath <abs .pptx> -LogoDir <dir> [-PngPath <abs .png>] [-PdfPath <abs .pdf>]

param(
  [Parameter(Mandatory = $true)][string]$PptxPath,
  [Parameter(Mandatory = $true)][string]$LogoDir,
  [string]$PngPath = "",
  [string]$PdfPath = ""
)

$ErrorActionPreference = "Stop"

function RGB([int]$r, [int]$g, [int]$b) { return $r + (256 * $g) + (65536 * $b) }

# --- sample palette, sampled straight off POPL_new.pdf ---------------------
$Deep   = RGB 0 57 127        # header / section titles
$Blue2  = RGB 0 70 158        # bottom band
$Steel  = RGB 71 106 173      # chevron, arrows
$Slate  = RGB 66 89 125       # chevron
$Navy   = RGB 34 55 135       # chevron
$Gold   = RGB 231 168 17      # the one accent
$Lav    = RGB 214 222 235     # diagram panels
$Mist   = RGB 239 244 248     # big containers
$Rule   = RGB 195 207 222
$Ink    = RGB 26 34 43
$Body   = RGB 62 74 87
$Faint  = RGB 124 138 153
$Paper  = RGB 255 255 255
$Dark   = RGB 46 52 64        # code block
$OnDark = RGB 216 222 233
$CodeKw = RGB 136 192 208
$CodeNo = RGB 235 203 139
$Purple = RGB 121 22 128      # ROPAS wordmark

$SANS = "Aptos"
$MONO = "Consolas"
$SERIF = "Times New Roman"

function New-Box {
  param($Sl, [double]$X, [double]$Y, [double]$W, [double]$H,
        [int]$Fill = -1, [int]$Stroke = -1, [double]$Weight = 1)
  $s = $Sl.Shapes.AddShape(1, $X, $Y, $W, $H)
  if ($Fill -lt 0) { $s.Fill.Visible = 0 } else { $s.Fill.Solid(); $s.Fill.ForeColor.RGB = $Fill }
  if ($Stroke -lt 0) { $s.Line.Visible = 0 }
  else { $s.Line.Visible = -1; $s.Line.ForeColor.RGB = $Stroke; $s.Line.Weight = $Weight }
  return $s
}

# Rounded rectangle. The sample rounds every panel; the radius is small enough
# that it reads as a softened edge rather than a pill.
function New-RBox {
  param($Sl, [double]$X, [double]$Y, [double]$W, [double]$H,
        [int]$Fill = -1, [int]$Stroke = -1, [double]$Weight = 1, [double]$R = 8)
  $s = $Sl.Shapes.AddShape(5, $X, $Y, $W, $H)
  $adj = $R / [Math]::Min($W, $H)
  if ($adj -gt 0.5) { $adj = 0.5 }
  $s.Adjustments.Item(1) = $adj
  if ($Fill -lt 0) { $s.Fill.Visible = 0 } else { $s.Fill.Solid(); $s.Fill.ForeColor.RGB = $Fill }
  if ($Stroke -lt 0) { $s.Line.Visible = 0 }
  else { $s.Line.Visible = -1; $s.Line.ForeColor.RGB = $Stroke; $s.Line.Weight = $Weight }
  return $s
}

function New-Rule {
  param($Sl, [double]$X1, [double]$Y1, [double]$X2, [double]$Y2,
        [int]$Color, [double]$Weight = 1, [switch]$Arrow)
  $l = $Sl.Shapes.AddLine($X1, $Y1, $X2, $Y2)
  $l.Line.ForeColor.RGB = $Color; $l.Line.Weight = $Weight
  if ($Arrow) { $l.Line.EndArrowheadStyle = 3; $l.Line.EndArrowheadLength = 1; $l.Line.EndArrowheadWidth = 1 }
  return $l
}

function New-Text {
  param($Sl, [string]$Text, [double]$X, [double]$Y, [double]$W, [double]$H,
        [double]$Size, [int]$Color, [switch]$Bold,
        [int]$Align = 1, [int]$VAlign = 1, [string]$Font = $SANS,
        [double]$Space = 0.95, [double]$Track = 0)
  $s = $Sl.Shapes.AddTextbox(1, $X, $Y, $W, $H)
  $tf = $s.TextFrame2
  # AddTextbox autosizes by default; that must be off before the text goes in,
  # otherwise the box grows and vertical anchoring silently breaks.
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
  if ($Track -ne 0) { $tr.Font.Spacing = $Track }
  $tr.ParagraphFormat.Alignment = $Align
  $tr.ParagraphFormat.SpaceWithin = $Space
  $s.Left = $X; $s.Top = $Y; $s.Width = $W; $s.Height = $H
  return $s
}

# Bulleted body copy — the sample leads every list item with a round bullet.
function New-Bullets {
  param($Sl, [string[]]$Items, [double]$X, [double]$Y, [double]$W, [double]$H,
        [double]$Size, [int]$Color, [double]$Space = 1.0)
  $t = ($Items | ForEach-Object { "•  $_" }) -join "`n"
  $s = New-Text $Sl $t $X $Y $W $H $Size $Color -Space $Space
  $s.TextFrame2.TextRange.ParagraphFormat.SpaceAfter = 5
  return $s
}

# Dark code plate. Keywords and literals get the sample's two accent tints so
# the block reads as code and not as a grey rectangle.
function New-Code {
  param($Sl, [string]$Text, [double]$X, [double]$Y, [double]$W, [double]$H,
        [double]$Size, [double]$PadX = 20, [double]$PadY = 12)
  [void](New-RBox $Sl $X $Y $W $H $Dark -R 7)
  $s = New-Text $Sl $Text ($X + $PadX) ($Y + $PadY) ($W - 2 * $PadX) ($H - 2 * $PadY) $Size $OnDark -Font $MONO -Space 1.1
  $tr = $s.TextFrame2.TextRange
  foreach ($m in [regex]::Matches($Text, '\b(int|unsigned|while|if|else|return|void)\b')) {
    $tr.Characters($m.Index + 1, $m.Length).Font.Fill.ForeColor.RGB = $CodeKw
  }
  foreach ($m in [regex]::Matches($Text, '\b\d+\b')) {
    $tr.Characters($m.Index + 1, $m.Length).Font.Fill.ForeColor.RGB = $CodeNo
  }
  return $s
}

# Section heading in the sample's voice: number in gold, title in deep blue,
# both large, no rules — the size alone carries the hierarchy.
function New-Section {
  param($Sl, [double]$X, [double]$Y, [double]$W, [string]$No, [string]$Title, [double]$Size = 25)
  [void](New-Text $Sl $No $X $Y 44 34 $Size $Gold -Bold -VAlign 3)
  [void](New-Text $Sl $Title ($X + 48) $Y ($W - 48) 34 $Size $Deep -Bold -VAlign 3)
}

function New-Chip {
  param($Sl, [string]$Text, [double]$X, [double]$Y, [double]$W, [double]$H,
        [int]$Fill, [int]$Color, [double]$Size = 10, [int]$Stroke = -1, [string]$Font = $SANS)
  [void](New-RBox $Sl $X $Y $W $H $Fill $Stroke 1 -R 6)
  [void](New-Text $Sl $Text $X $Y $W $H $Size $Color -Bold -Align 2 -VAlign 3 -Font $Font)
}

function New-Node {
  param($Sl, [string]$Title, [string]$Sub, [double]$X, [double]$Y, [double]$W, [double]$H,
        [int]$Fill, [int]$Stroke, [int]$TitleColor, [int]$SubColor, [double]$TSize = 12)
  [void](New-RBox $Sl $X $Y $W $H $Fill $Stroke 1 -R 8)
  [void](New-Text $Sl $Title ($X + 6) ($Y + 8) ($W - 12) 18 $TSize $TitleColor -Bold -Align 2)
  [void](New-Text $Sl $Sub ($X + 8) ($Y + 26) ($W - 16) ($H - 31) 9.5 $SubColor -Align 2)
}

function New-Judg {
  param($Sl, [string]$Text, [double]$Cx, [double]$Y, [double]$BarW,
        [int]$BarColor, [int]$TextColor, [double]$Size = 10, [double]$BarWeight = 1)
  [void](New-Rule $Sl ($Cx - $BarW / 2) $Y ($Cx + $BarW / 2) $Y $BarColor $BarWeight)
  [void](New-Text $Sl $Text ($Cx - ($BarW + 60) / 2) ($Y + 2) ($BarW + 60) 17 $Size $TextColor -Align 2 -Font $MONO)
}

# The sample's corner motif: a cascade of 45° chevrons running off the page
# edge. $Dir is +1 for the left corner (pointing right), -1 for the right.
# Move every shape added since $From — lets each band be authored in its own
# coordinates and then settled into the page budget in one place.
function Move-Band {
  param($Sl, [int]$From, [double]$Dy)
  for ($i = $From + 1; $i -le $Sl.Shapes.Count; $i++) { $Sl.Shapes.Item($i).Top = $Sl.Shapes.Item($i).Top + $Dy }
}

function New-Chevron {
  param($Sl, [double]$X, [double]$Y, [double]$R, [double]$T, [int]$Color, [int]$Dir = 1)
  $ff = $Sl.Shapes.BuildFreeform(0, $X, $Y)
  $ff.AddNodes(0, 0, ($X + $Dir * $R), ($Y + $R))
  $ff.AddNodes(0, 0, $X, ($Y + 2 * $R))
  $ff.AddNodes(0, 0, $X, ($Y + 2 * $R - $T))
  $ff.AddNodes(0, 0, ($X + $Dir * ($R - $T)), ($Y + $R))
  $ff.AddNodes(0, 0, $X, ($Y + $T))
  $ff.AddNodes(0, 0, $X, $Y)
  $s = $ff.ConvertToShape()
  $s.Fill.Solid(); $s.Fill.ForeColor.RGB = $Color
  $s.Line.Visible = 0
  return $s
}

$ownedApp = $false; $app = $null; $pres = $null
try {
  try { $app = [Runtime.InteropServices.Marshal]::GetActiveObject("PowerPoint.Application") }
  catch { $app = New-Object -ComObject PowerPoint.Application; $ownedApp = $true }
  $app.Visible = -1

  $pres = $app.Presentations.Open($PptxPath, 0, 0, -1)
  $SW = $pres.PageSetup.SlideWidth
  $SH = $pres.PageSetup.SlideHeight
  if ($pres.Slides.Count -eq 0) { [void]$pres.Slides.Add(1, 12) }
  $sl = $pres.Slides.Item(1)
  $sl.CustomLayout = $pres.SlideMaster.CustomLayouts.Item(7)
  while ($sl.Shapes.Count -gt 0) { $sl.Shapes.Item(1).Delete() }

  $M = 52; $CW = 1086
  $a = 52; $b = 422; $c = 792
  $col = 344; $two = 714

  [void](New-Box $sl 0 0 $SW $SH $Paper)

  # ============================================================ HEADER
  [void](New-Box $sl 0 0 $SW 196 $Deep)
  [void](New-Text $sl "SIGPL 여름학교 2026   ·   포스터 세션" $M 26 $CW 16 11.5 $Gold -Bold -Align 2 -Track 3)
  [void](New-Text $sl "Big-Step 증명나무 합성을 통한 정적 분석기 공격" 100 46 990 90 38 $Paper -Bold -Align 2 -VAlign 3 -Space 0.92)
  [void](New-Text $sl "프로그램이 아니라, 그 프로그램의 실행 의미를 합성한다" $M 138 $CW 24 15.5 $Lav -Align 2 -VAlign 3)
  [void](New-Rule $sl 470 170 720 170 $Steel 1)
  [void](New-Text $sl "정원준     지도교수  이광근     서울대학교 프로그래밍 연구실 ROPAS" $M 174 $CW 20 12.5 $Lav -Align 2 -VAlign 3)

  # ============================================================ LEAD
  [void](New-Text $sl "왜 증명나무를 합성하는가" $M 212 $CW 16 11 $Gold -Bold -Align 2 -Track 2)
  $Quote = "{0}프로그램을 먼저 합성하면, 그 프로그램에 실행 의미가 있는지조차 알 수 없다.{1}" -f [char]0x201C, [char]0x201D
  [void](New-Text $sl $Quote $M 234 $CW 44 25 $Ink -Bold -Align 2 -VAlign 3)
  [void](New-Text $sl "그래서 프로그램 대신 실행 의미 — Big-Step 증명나무 — 를 합성한다. 프로그램은 그 증명의 결론으로 따라 나온다." $M 282 $CW 22 13.5 $Body -Align 2 -VAlign 3)
  [void](New-Text $sl "프로그램이 멈추는지조차 미리 알 수 없다 (Rice's Theorem). 반대로 유한한 증명나무가 있다는 것은 곧 그 실행이 존재한다는 뜻이다." $M 306 $CW 18 11 $Faint -Align 2 -VAlign 3)

  # ============================================================ BAND 1
  # -- 01 the problem
  New-Section $sl $a 340 $col "01" "문제 설정"
  [void](New-Text $sl "분석기가 가짜 경보를 내거나 안전성을 잃는 가장 작은 프로그램을, 사람 없이 자동으로 찾는다." $a 390 $col 44 13.5 $Ink -Bold)
  [void](New-Text $sl "분석기는 C를 분석하지만, 실제 분석은 C를 단순화한 CIL과 그로부터 만든 CFG 위에서 일어난다. 모든 C 문법이 공격에 필요한 것은 아니다." $a 446 $col 52 11 $Body)
  [void](New-Text $sl "실제 분석 경로" $a 506 200 14 9.5 $Faint -Bold -Track 1.2)
  $cy = 526
  New-Chip $sl "C"     $a          $cy 48 30 $Paper $Deep 12 $Rule
  [void](New-Rule $sl ($a + 52)  ($cy + 15) ($a + 66)  ($cy + 15) $Steel 1.2 -Arrow)
  New-Chip $sl "CIL"   ($a + 70)  $cy 56 30 $Paper $Deep 12 $Rule
  [void](New-Rule $sl ($a + 130) ($cy + 15) ($a + 144) ($cy + 15) $Steel 1.2 -Arrow)
  New-Chip $sl "CFG"   ($a + 148) $cy 58 30 $Paper $Deep 12 $Rule
  [void](New-Rule $sl ($a + 210) ($cy + 15) ($a + 224) ($cy + 15) $Steel 1.2 -Arrow)
  New-Chip $sl "분석기" ($a + 228) $cy 76 30 $Deep $Paper 11
  [void](New-Text $sl "분석 대상은 C가 아니라, 그 아래로 내려간 CIL과 CFG다." $a 566 $col 20 10.5 $Faint)
  [void](New-RBox $sl $a 596 $col 58 $Lav -R 8)
  [void](New-Text $sl "그래서 공격에 필요한 만큼만 담은 더 작은 언어 CIL--를 새로 정의한다." ($a + 16) 596 ($col - 32) 58 12.5 $Deep -Bold -VAlign 3)
  [void](New-Text $sl "찾아낸 공격은 분석기를 강화하는 지침이 되고, 거꾸로 난독화에도 쓸 수 있다." $a 664 $col 34 10.5 $Body)

  # -- 02 the language
  New-Section $sl $b 340 $col "02" "언어: CIL--"
  [void](New-RBox $sl $b 390 $col 54 $Lav -R 8)
  [void](New-Text $sl "대상 분석기는 Sparrow. C를 CIL 1.7.3으로 낮춘 뒤 그 위에서 분석한다. CIL--는 그 CIL의 부분집합이자 합성 · 실행 · 증명의 기준 언어다." ($b + 14) 390 ($col - 28) 54 11 $Deep -Bold -VAlign 3)
  [void](New-Text $sl "포함" $b 456 60 14 9.5 $Gold -Bold -Track 1.2)
  [void](New-Bullets $sl @("int / unsigned int", "직접 함수 호출 — 재귀와 상호재귀", "if · loop · break · continue · return", "포인터와 배열 문법") $b 472 $col 64 11 $Ink)
  [void](New-Text $sl "제외" $b 544 60 14 9.5 $Gold -Bold -Track 1.2)
  [void](New-Bullets $sl @("cast · float · struct/union · 문자열", "switch · goto · varargs · typedef · enum") $b 560 $col 34 11 $Body)
  [void](New-RBox $sl $b 602 $col 56 $Paper $Rule 1 -R 8)
  [void](New-Box $sl $b 610 4 40 $Gold)
  [void](New-Text $sl "cast-free" ($b + 18) 608 200 14 10 $Deep -Bold)
  [void](New-Text $sl "명시적 cast와 프론트엔드가 몰래 넣는 암묵 변환을 구분할 필요가 없도록, CastE를 아예 두지 않는다." ($b + 18) 624 ($col - 34) 30 10.5 $Ink)
  [void](New-Text $sl "하나의 GADT, 두 개의 mode" $b 666 220 14 9.5 $Faint -Bold -Track 1.2)
  New-Node $sl "Syntax.ground" "hole 불가 — 실행 · 검증" $b 682 166 44 $Paper $Rule $Deep $Body 12
  New-Node $sl "Syntax.holed" "ExpHole · StmtSeqHole" ($b + 178) 682 166 44 $Lav $Lav $Deep $Body 12

  # -- 03 what counts as an attack
  New-Section $sl $c 340 $col "03" "공격의 정의"
  [void](New-Text $sl "main이 0을 반환하며 정상 종료한 실행만 비교한다. 그 시점에 살아 있는 모든 지역 memory binding이 관찰 대상." $c 390 $col 54 12.5 $Ink -Bold)
  [void](New-RBox $sl $c 452 $col 32 $Deep -R 7)
  [void](New-Text $sl "안전성 실패" ($c + 16) 452 100 32 11 $Paper -Bold -VAlign 3)
  [void](New-Text $sl "구체값 ∉ 분석 결과" ($c + 118) 452 ($col - 134) 32 11 $Lav -Align 3 -VAlign 3)
  [void](New-RBox $sl $c 488 $col 32 $Lav -R 7)
  [void](New-Text $sl "정밀도 실패" ($c + 16) 488 100 32 11 $Deep -Bold -VAlign 3)
  [void](New-Text $sl "분석 결과 ⊋ {구체값}" ($c + 118) 488 ($col - 134) 32 11 $Deep -Align 3 -VAlign 3)
  [void](New-Text $sl "찾아낸 공격 예시" $c 530 200 14 9.5 $Faint -Bold -Track 1.2)
  [void](New-Code $sl "x = 1;`nwhile (-x) { x = 0; }`nx = x * x;" $c 548 $col 68 11)
  [void](New-Text $sl "구체 실행  x = 0" $c 624 160 18 10.5 $Ink -Bold -Font $MONO)
  [void](New-Text $sl "분석 결과  x |-> [-inf, inf]" ($c + 160) 624 ($col - 160) 18 10.5 $Steel -Bold -Align 3 -Font $MONO)
  [void](New-Text $sl "guard가 x가 아니라 -x라 종료 후 필터가 약하고, x * x는 두 피연산자가 같은 변수라는 상관관계를 잃는다." $c 648 $col 36 10.5 $Body)
  [void](New-Text $sl "* 이전 자체 분석기 엔진에서 발견" $c 688 $col 16 9 $Faint)

  # ============================================================ BAND 2 — hero
  New-Section $sl $a 744 $CW "04" "잎에서 뿌리로, 작은 조각부터 쌓아 올린다"
  [void](New-RBox $sl 36 784 ($SW - 72) 212 $Mist $Rule 1 -R 14)

  [void](New-Code $sl "int main() {`n  int x;`n  x = 1;`n  return x;`n}" $a 800 210 106 11)
  [void](New-Text $sl "EConst, LVar 같은 가장 작은 조각에서 시작해 뿌리까지 올라간다. 그림의 위에서 아래가 합성 순서다. 프로그램은 뿌리의 결론으로 따라 나온다." $a 916 264 62 11 $Body)

  $TX = 350; $TW = 430
  $cA = $TX + 92;  $wA = 186
  $cB = $TX + 322; $wB = 200
  $cRoot = $TX + $TW / 2
  $ty = 804; $dy = 21
  foreach ($ax in @(($cA - 92), ($cA + 6), ($cB - 46))) {
    [void](New-Rule $sl $ax ($ty - 4) ($ax + 88) ($ty - 4) $Rule 1)
  }
  [void](New-Text $sl "[LVar] x => s0+0" ($cA - 92) $ty 88 16 10 $Body -Align 2 -Font $MONO)
  [void](New-Text $sl "[EConst] 1 => 1"  ($cA + 6)  $ty 88 16 10 $Body -Align 2 -Font $MONO)
  [void](New-Text $sl "[LVar] x => s0+0" ($cB - 46) $ty 88 16 10 $Body -Align 2 -Font $MONO)
  New-Judg $sl "[ISet] x = 1; => {x |-> 1}"           $cA ($ty + $dy)      $wA $Rule $Ink
  New-Judg $sl "[ELval] x => 1"                       $cB ($ty + $dy)      $wB $Rule $Ink
  New-Judg $sl "[SInstr] instr[1] => Normal"          $cA ($ty + 2 * $dy)  $wA $Rule $Ink
  New-Judg $sl "[SReturnSome] return x; => Return(1)" $cB ($ty + 2 * $dy)  $wB $Rule $Ink
  New-Judg $sl "[BSeq] block[2] => Return(1)"    $cRoot ($ty + 3 * $dy) $TW $Rule $Ink
  New-Judg $sl "[FReturn] main() => Return(1)"   $cRoot ($ty + 4 * $dy) $TW $Rule $Ink
  New-Judg $sl "[PMainReturn] main() => 1"       $cRoot ($ty + 5 * $dy) $TW $Deep $Deep 11 2
  [void](New-Rule $sl $TX ($ty + 6 * $dy) ($TX + $TW) ($ty + 6 * $dy) $Deep 2)
  [void](New-Text $sl "proof_size(t) = 1 + sum of premise sizes" $TX ($ty + 6 * $dy + 6) $TW 16 9.5 $Faint -Align 2 -Font $MONO)

  [void](New-RBox $sl 812 800 326 76 $Paper $Rule 1 -R 8)
  [void](New-Box $sl 812 812 4 52 $Gold)
  [void](New-Text $sl "크기 순서대로 pool에 쌓는다" 832 808 290 18 12 $Deep -Bold)
  [void](New-Text $sl "규칙마다 이미 만들어 둔 더 작은 조각만 꺼내 쓴다. 호출된 함수의 증명도 언제나 진부분나무이므로 재귀·상호재귀가 잘 정의된다." 832 828 290 42 10.5 $Body)
  [void](New-RBox $sl 812 888 326 84 $Paper $Rule 1 -R 8)
  [void](New-Box $sl 812 902 4 56 $Gold)
  [void](New-Text $sl "메모리가 항상 따라 붙는다" 832 896 290 18 12 $Deep -Bold)
  [void](New-Text $sl "완전한 프로그램은 스스로 메모리를 정하지만, 조각은 앞뒤 메모리의 관계만 안다. 메모리를 나중으로 미루면 정지 문제에 빠지므로, 조각을 만들 때 전후 메모리를 확정한다." 832 916 290 50 10.5 $Body)

  # ============================================================ BAND 3
  $band3 = $sl.Shapes.Count
  # -- 05 holes and unification
  New-Section $sl $a 1008 $col "05" "실행 안 된 자리는 hole로"
  [void](New-Code $sl "if (x || ?H1) {`n  return 0;`n} else {`n  ?H2`n}" $a 1058 230 100 11)
  New-Chip $sl "?H1" $a 1164 44 22 $Deep $Paper 10 -1 $MONO
  [void](New-Text $sl "short-circuit로 평가되지 않은 오른쪽 피연산자 — ExpHole" ($a + 54) 1164 ($col - 54) 30 10.5 $Ink)
  New-Chip $sl "?H2" $a 1198 44 22 $Steel $Paper 10 -1 $MONO
  [void](New-Text $sl "선택되지 않은 branch, 또는 return · break · continue 뒤에 잘린 block 꼬리 — StmtSeqHole" ($a + 54) 1198 ($col - 54) 42 10.5 $Ink)
  [void](New-RBox $sl $a 1244 $col 30 $Deep -R 7)
  [void](New-Text $sl "실행된 자리에는 hole이 남을 수 없다." ($a + 16) 1244 ($col - 32) 30 11 $Paper -Bold -VAlign 3)
  [void](New-Text $sl "같은 정적 위치가 loop · 재귀로 여러 번 실행되면 그 조각들이 서로 맞아야 한다. 타입 추론에서와 같은 unification으로 맞추고, 나무와 substitution을 따로 들고 다닌다." $a 1282 $col 46 10.5 $Body)

  # -- 06 fill the holes, then hand it to the analyser
  New-Section $sl $b 1008 $two "06" "hole을 채워 분석기에 넣는다"
  [void](New-Text $sl "hole 자리는 어차피 실행되지 않았다. 그래서 아무 코드나 채워 넣어도 이 증명나무가 말하는 실행 의미는 바뀌지 않는다. 문맥이 맞을 필요도 없다. 새로운 실행이 생기지 않도록 함수 호출만 넣지 않는다." $b 1058 $two 34 11.5 $Ink)
  [void](New-RBox $sl 410 1096 740 128 $Mist $Rule 1 -R 14)
  New-Node $sl "완성된 holed 증명나무" "미실행 자리는 아직 hole" $b 1133 152 54 $Paper $Rule $Deep $Body 11.5
  [void](New-Rule $sl ($b + 156) 1160 ($b + 172) 1160 $Steel 1.4 -Arrow)
  New-Node $sl "hole 채우기" "아무 코드나 — 호출만 제외" ($b + 174) 1133 138 54 $Lav $Lav $Deep $Body 11.5
  [void](New-Rule $sl ($b + 316) 1160 ($b + 332) 1160 $Steel 1.4 -Arrow)
  New-Node $sl "구체 CIL-- 프로그램" "hole 없는 완성된 코드" ($b + 334) 1133 140 54 $Deep $Deep $Paper $Lav 11.5
  [void](New-Rule $sl ($b + 476) 1153 ($b + 494) 1129 $Steel 1.4 -Arrow)
  [void](New-Rule $sl ($b + 476) 1167 ($b + 494) 1191 $Steel 1.4 -Arrow)
  New-Node $sl "증명나무의 구체값" "실제 실행 의미" ($b + 496) 1105 130 46 $Paper $Rule $Deep $Body 11
  New-Node $sl "분석기의 분석 결과" "어림잡은 값" ($b + 496) 1169 130 46 $Paper $Rule $Deep $Body 11
  [void](New-Rule $sl ($b + 628) 1129 ($b + 646) 1153 $Steel 1.4 -Arrow)
  [void](New-Rule $sl ($b + 628) 1191 ($b + 646) 1167 $Steel 1.4 -Arrow)
  [void](New-RBox $sl ($b + 646) 1133 68 54 $Deep -R 8)
  [void](New-Text $sl "비교" ($b + 646) 1133 68 54 12.5 $Paper -Bold -Align 2 -VAlign 3)
  [void](New-RBox $sl $b 1236 350 30 $Deep -R 7)
  [void](New-Text $sl "구체값 ∉ 분석 결과   →   안전성 공격" ($b + 16) 1236 322 30 11 $Paper -Bold -VAlign 3)
  [void](New-RBox $sl ($b + 364) 1236 350 30 $Lav -R 7)
  [void](New-Text $sl "분석 결과 ⊋ {구체값}   →   정밀도 공격" ($b + 380) 1236 322 30 11 $Deep -Bold -VAlign 3)
  [void](New-Text $sl "정밀도 공격은 튜링 완전한 부분집합이기만 하면 반드시 존재한다 (Rice's Theorem). 안전성 공격은 버그를 찾는 일이라, 언어 기능이 많을수록 유리하다." $b 1276 $two 32 10.5 $Body)

  Move-Band $sl $band3 -16

  # ============================================================ BAND 4
  $band4 = $sl.Shapes.Count
  New-Section $sl $a 1360 $CW "07" "정말 올바른 공격인가"
  [void](New-Text $sl "공격이 성공했다고 말하려면, 분석기가 전제하는 실행 의미와 우리가 CIL--에 준 실행 의미가 같아야 한다." $a 1406 $CW 22 13 $Ink -Bold)
  [void](New-RBox $sl $a 1438 340 84 $Deep -R 10)
  [void](New-Text $sl "아무도 실행 의미를 엄밀히 적어두지 않았다" ($a + 20) 1446 302 18 11.5 $Paper -Bold)
  [void](New-Text $sl "C의 ISO 표준은 자연어로 되어 있고, CIL에도 엄밀한 실행 의미가 없다. 분석기 역시 sound in design이라고 말할 뿐 concrete semantics를 정의하지 않는다." ($a + 20) 1466 302 50 10 $Lav)
  [void](New-Text $sl "우리에게는 CIL--의 Big-Step 실행 의미가 있다. 비결정성이 남아 있으면 공격에 성공한 것처럼 보여도 사실은 비결정성 탓일 수 있으므로, 하나씩 없앤다." $a 1530 340 36 10.5 $Body)

  # -- nondeterminism table: what C leaves open, and where CIL-- closes it
  $tx = 412; $tw = 726
  $w1 = 156; $w2 = 186; $w3 = 178; $w4 = 206
  $x2 = $tx + $w1; $x3 = $x2 + $w2; $x4 = $x3 + $w3
  [void](New-RBox $sl $tx 1438 $tw 22 $Lav -R 6)
  [void](New-Text $sl "예"     ($tx + 10) 1438 $w1 22 9 $Deep -Bold -Track 1 -VAlign 3)
  [void](New-Text $sl "C"      ($x2 + 4)  1438 $w2 22 9 $Deep -Bold -Track 1 -VAlign 3)
  [void](New-Text $sl "CIL"    ($x3 + 4)  1438 $w3 22 9 $Deep -Bold -Track 1 -VAlign 3)
  [void](New-Text $sl "CIL--"  ($x4 + 4)  1438 $w4 22 9 $Deep -Bold -Track 1 -VAlign 3)
  $rows = @(
    @("f() + g()",      "계산 순서가 정해지지 않음", "호출이 식에 들어가지 않음", "없앰"),
    @("i = i++ + 1;",   "undefined behavior",       "i++ 문법이 없음",          "없앰"),
    @("int x; use(x);", "indeterminate value",      "indeterminate value",      "합성 시 만들지 않음"),
    @("`"a`" == `"a`"", "true / false 모두 가능",   "여전히 비결정적",           "문자열이 없음"),
    @("char c = -1;",   "-1 또는 255",              "여전히 비결정적",           "char가 없음"),
    @("malloc(n)",      "주소가 비결정적",           "fresh object",             "포인터가 없음")
  )
  $ry = 1462
  foreach ($r in $rows) {
    [void](New-Text $sl $r[0] ($tx + 10) $ry $w1 14 9 $Ink -Bold -Font $MONO -VAlign 3)
    [void](New-Text $sl $r[1] ($x2 + 4)  $ry $w2 14 9 $Body -VAlign 3)
    [void](New-Text $sl $r[2] ($x3 + 4)  $ry $w3 14 9 $Body -VAlign 3)
    [void](New-Text $sl $r[3] ($x4 + 4)  $ry $w4 14 9 $Deep -Bold -VAlign 3)
    [void](New-Rule $sl $tx ($ry + 15) ($tx + $tw) ($ry + 15) $Rule 0.75)
    $ry += 16
  }

  Move-Band $sl $band4 -30

  # ============================================================ FOOT
  # Corner motif from the sample: chevrons cascading off both page edges,
  # then the logo row, then the deep blue band.
  $chR = 82; $chT = 46; $chY = 1494; $chStep = 32
  $chCols = @($Gold, $Navy, $Slate, $Steel)
  for ($i = 0; $i -lt 4; $i++) {
    [void](New-Chevron $sl -36 ($chY + $i * $chStep) $chR $chT $chCols[$i] 1)
    [void](New-Chevron $sl ($SW + 36) ($chY + $i * $chStep) $chR $chT $chCols[$i] -1)
  }

  # Seoul National University
  [void]$sl.Shapes.AddPicture((Join-Path $LogoDir "snu-navy.png"), 0, -1, 104, 1560, 62, 64)
  [void](New-Text $sl "SEOUL"      178 1562 200 22 17 $Deep -Bold -Font $SERIF -Track 3)
  [void](New-Text $sl "NATIONAL"   178 1586 200 15 10.5 $Deep -Font $SERIF -Track 2.4)
  [void](New-Text $sl "UNIVERSITY" 178 1602 200 15 10.5 $Deep -Font $SERIF -Track 2.4)

  # SIGPL — the venue this poster is actually for
  [void]$sl.Shapes.AddPicture((Join-Path $LogoDir "SIGPL_logo.png"), 0, -1, 563, 1556, 64, 65)
  [void](New-Text $sl "한국정보과학회 프로그래밍언어연구회" 445 1626 300 14 8.5 $Faint -Align 2)

  # ROPAS
  [void]$sl.Shapes.AddPicture((Join-Path $LogoDir "ropas-purple.png"), 0, -1, 884, 1560, 62, 62)
  [void](New-Text $sl "Programming"          958 1560 200 22 15.5 $Purple -Bold -Font $SERIF)
  [void](New-Text $sl "Research Laboratory"  958 1584 200 22 15.5 $Purple -Bold -Font $SERIF)

  [void](New-Box $sl 0 1647 $SW ($SH - 1647) $Blue2)

  $pres.Save()
  if ($PngPath -ne "") {
    if (Test-Path $PngPath) { Remove-Item $PngPath -Force }
    $sl.Export($PngPath, "PNG", 1400, 1980)
  }
  if ($PdfPath -ne "") {
    if (Test-Path $PdfPath) { Remove-Item $PdfPath -Force }
    $pres.SaveCopyAs($PdfPath, 32)
  }
  $pres.Close(); $pres = $null
  Write-Output "OK $PptxPath"
} finally {
  if ($null -ne $pres) { try { $pres.Close() } catch {} }
  if ($ownedApp -and $null -ne $app) { try { $app.Quit() } catch {} }
  if ($null -ne $app) { try { [void][Runtime.InteropServices.Marshal]::ReleaseComObject($app) } catch {} }
  [GC]::Collect(); [GC]::WaitForPendingFinalizers()
}
