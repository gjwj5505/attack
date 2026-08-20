# SIGPL 여름학교 2026 포스터 세션 — poster drawn into an existing A2-portrait pptx.
#
# Palette discipline: two analogous SNU blues (deep + steel) plus neutrals.
# Emphasis comes from value and fill, never from a third hue. Both logos are
# recoloured to white monochrome so they sit on the deep header without
# introducing a third colour.
#
# Usage:
#   powershell -ExecutionPolicy Bypass -File build_sigpl_poster.ps1 `
#     -PptxPath <abs .pptx> -LogoDir <dir with snu-white.png, ropas-white.png> `
#     [-PngPath <abs .png>] [-PdfPath <abs .pdf>]

param(
  [Parameter(Mandatory = $true)][string]$PptxPath,
  [Parameter(Mandatory = $true)][string]$LogoDir,
  [string]$PngPath = "",
  [string]$PdfPath = ""
)

$ErrorActionPreference = "Stop"

function RGB([int]$r, [int]$g, [int]$b) { return $r + (256 * $g) + (65536 * $b) }

$Deep  = RGB 0 56 112        # SNU blue
$Steel = RGB 62 124 180      # analogous mid blue
$Pale  = RGB 226 236 246
$Mist  = RGB 241 246 251
$Rule  = RGB 198 214 230
$Ink   = RGB 18 30 44
$Body  = RGB 66 84 102
$Faint = RGB 126 146 166
$Paper = RGB 255 255 255
$Dark  = RGB 8 24 41
$OnDark = RGB 218 232 244

$SANS = "Aptos"
$MONO = "Consolas"

function New-Box {
  param($Sl, [double]$X, [double]$Y, [double]$W, [double]$H,
        [int]$Fill = -1, [int]$Stroke = -1, [double]$Weight = 1)
  $s = $Sl.Shapes.AddShape(1, $X, $Y, $W, $H)
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

function New-Section {
  param($Sl, [double]$X, [double]$Y, [double]$W, [string]$No, [string]$Title)
  [void](New-Rule $Sl $X $Y ($X + $W) $Y $Deep 2.5)
  [void](New-Text $Sl $No $X ($Y + 13) 42 28 24 $Steel -Bold -VAlign 3)
  [void](New-Text $Sl $Title ($X + 46) ($Y + 12) ($W - 46) 30 19 $Ink -Bold -VAlign 3)
}

function New-Chip {
  param($Sl, [string]$Text, [double]$X, [double]$Y, [double]$W, [double]$H,
        [int]$Fill, [int]$Color, [double]$Size = 10, [int]$Stroke = -1, [string]$Font = $SANS)
  [void](New-Box $Sl $X $Y $W $H $Fill $Stroke 1)
  [void](New-Text $Sl $Text $X $Y $W $H $Size $Color -Bold -Align 2 -VAlign 3 -Font $Font)
}

function New-Node {
  param($Sl, [string]$Title, [string]$Sub, [double]$X, [double]$Y, [double]$W, [double]$H,
        [int]$Fill, [int]$Stroke, [int]$TitleColor, [int]$SubColor, [double]$TSize = 12)
  [void](New-Box $Sl $X $Y $W $H $Fill $Stroke 1)
  [void](New-Text $Sl $Title ($X + 6) ($Y + 8) ($W - 12) 18 $TSize $TitleColor -Bold -Align 2)
  [void](New-Text $Sl $Sub ($X + 8) ($Y + 26) ($W - 16) ($H - 31) 9.5 $SubColor -Align 2)
}

function New-Judg {
  param($Sl, [string]$Text, [double]$Cx, [double]$Y, [double]$BarW,
        [int]$BarColor, [int]$TextColor, [double]$Size = 10, [double]$BarWeight = 1)
  [void](New-Rule $Sl ($Cx - $BarW / 2) $Y ($Cx + $BarW / 2) $Y $BarColor $BarWeight)
  [void](New-Text $Sl $Text ($Cx - ($BarW + 60) / 2) ($Y + 2) ($BarW + 60) 17 $Size $TextColor -Align 2 -Font $MONO)
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
  [void](New-Box $sl 0 0 $SW 206 $Deep)
  [void](New-Box $sl 0 200 $SW 6 $Steel)
  [void]$sl.Shapes.AddPicture((Join-Path $LogoDir "snu-white.png"),   0, -1, $M,   62, 82, 85)
  [void]$sl.Shapes.AddPicture((Join-Path $LogoDir "ropas-white.png"), 0, -1, 1072, 73, 66, 66)
  [void](New-Text $sl "SIGPL 여름학교 2026   ·   포스터 세션" 150 42 890 16 11 $Steel -Bold -Align 2 -Track 2)
  [void](New-Text $sl "Big-Step 증명나무 합성을 통한 정적 분석기 공격" 150 64 890 48 34 $Paper -Bold -Align 2 -VAlign 3)
  [void](New-Text $sl "프로그램이 아니라, 그 프로그램의 실행 의미를 합성한다" 150 116 890 24 15 $Pale -Align 2 -VAlign 3)
  [void](New-Rule $sl 400 148 790 148 $Steel 1)
  [void](New-Text $sl "정원준     지도교수  이광근     서울대학교 프로그래밍 연구실 ROPAS" 150 158 890 22 12.5 $Pale -Align 2 -VAlign 3)

  # ============================================================ LEAD
  [void](New-Text $sl "왜 증명나무를 합성하는가" $M 228 300 16 10.5 $Steel -Bold -Track 2)
  [void](New-Text $sl "프로그램을 먼저 합성하면, 그 프로그램에 실행 의미가 있는지조차 알 수 없다." $M 250 $CW 32 21.5 $Ink -Bold -VAlign 3)
  [void](New-Text $sl "그래서 프로그램 대신 실행 의미 — Big-Step 증명나무 — 를 합성한다. 프로그램은 그 증명의 결론으로 따라 나온다." $M 288 $CW 22 14 $Body -VAlign 3)
  [void](New-Text $sl "프로그램이 멈추는지조차 미리 알 수 없다 (Rice's Theorem). 반대로 유한한 증명나무가 있다는 것은 곧 그 실행이 존재한다는 뜻이다." $M 314 $CW 18 11 $Faint -VAlign 3)

  # ============================================================ BAND 1
  # -- 01 the problem
  New-Section $sl $a 350 $col "01" "문제 설정"
  [void](New-Text $sl "분석기가 가짜 경보를 내거나 안전성을 잃는 가장 작은 프로그램을, 사람 없이 자동으로 찾는다." $a 400 $col 44 13.5 $Ink -Bold)
  [void](New-Text $sl "분석기는 C를 분석하지만, 실제 분석은 C를 단순화한 CIL과 그로부터 만든 CFG 위에서 일어난다. 모든 C 문법이 공격에 필요한 것은 아니다." $a 456 $col 52 11 $Body)
  [void](New-Text $sl "실제 분석 경로" $a 516 200 14 9.5 $Faint -Bold -Track 1.2)
  $cy = 536
  New-Chip $sl "C"     $a          $cy 48 30 $Paper $Deep 12 $Rule
  [void](New-Rule $sl ($a + 52)  ($cy + 15) ($a + 66)  ($cy + 15) $Steel 1.2 -Arrow)
  New-Chip $sl "CIL"   ($a + 70)  $cy 56 30 $Paper $Deep 12 $Rule
  [void](New-Rule $sl ($a + 130) ($cy + 15) ($a + 144) ($cy + 15) $Steel 1.2 -Arrow)
  New-Chip $sl "CFG"   ($a + 148) $cy 58 30 $Paper $Deep 12 $Rule
  [void](New-Rule $sl ($a + 210) ($cy + 15) ($a + 224) ($cy + 15) $Steel 1.2 -Arrow)
  New-Chip $sl "분석기" ($a + 228) $cy 76 30 $Deep $Paper 11
  [void](New-Text $sl "분석 대상은 C가 아니라, 그 아래로 내려간 CIL과 CFG다." $a 576 $col 20 10.5 $Faint)
  [void](New-Box $sl $a 606 $col 58 $Pale)
  [void](New-Text $sl "그래서 공격에 필요한 만큼만 담은 더 작은 언어 CIL--를 새로 정의한다." ($a + 16) 606 ($col - 32) 58 12.5 $Deep -Bold -VAlign 3)
  [void](New-Text $sl "찾아낸 공격은 분석기를 강화하는 지침이 되고, 거꾸로 난독화에도 쓸 수 있다." $a 674 $col 34 10.5 $Body)

  # -- 02 the language
  New-Section $sl $b 350 $col "02" "언어: CIL--"
  [void](New-Box $sl $b 400 $col 54 $Pale)
  [void](New-Text $sl "대상 분석기는 Sparrow. C를 CIL 1.7.3으로 낮춘 뒤 그 위에서 분석한다. CIL--는 그 CIL의 부분집합이자 합성 · 실행 · 증명의 기준 언어다." ($b + 14) 400 ($col - 28) 54 11 $Deep -Bold -VAlign 3)
  [void](New-Text $sl "포함" $b 466 60 14 9.5 $Steel -Bold -Track 1.2)
  [void](New-Text $sl "int / unsigned int`n직접 함수 호출 — 재귀와 상호재귀`nif · loop · break · continue · return`n포인터와 배열 문법" $b 482 $col 64 11 $Ink)
  [void](New-Text $sl "제외" $b 554 60 14 9.5 $Steel -Bold -Track 1.2)
  [void](New-Text $sl "cast · float · struct/union · 문자열`nswitch · goto · varargs · typedef · enum" $b 570 $col 34 11 $Body)
  [void](New-Box $sl $b 612 $col 56 $Paper $Rule 1)
  [void](New-Box $sl $b 612 4 56 $Steel)
  [void](New-Text $sl "cast-free" ($b + 18) 618 200 14 10 $Steel -Bold)
  [void](New-Text $sl "명시적 cast와 프론트엔드가 몰래 넣는 암묵 변환을 구분할 필요가 없도록, CastE를 아예 두지 않는다." ($b + 18) 634 ($col - 34) 30 10.5 $Ink)
  [void](New-Text $sl "하나의 GADT, 두 개의 mode" $b 676 220 14 9.5 $Faint -Bold -Track 1.2)
  New-Node $sl "Syntax.ground" "hole 불가 — 실행 · 검증" $b 692 166 44 $Paper $Rule $Deep $Body 12
  New-Node $sl "Syntax.holed" "ExpHole · StmtSeqHole" ($b + 178) 692 166 44 $Pale $Pale $Deep $Body 12

  # -- 03 what counts as an attack
  New-Section $sl $c 350 $col "03" "공격의 정의"
  [void](New-Text $sl "main이 0을 반환하며 정상 종료한 실행만 비교한다. 그 시점에 살아 있는 모든 지역 memory binding이 관찰 대상." $c 400 $col 54 12.5 $Ink -Bold)
  [void](New-Box $sl $c 462 $col 32 $Deep)
  [void](New-Text $sl "안전성 실패" ($c + 14) 462 100 32 11 $Paper -Bold -VAlign 3)
  [void](New-Text $sl "구체값 ∉ 분석 결과" ($c + 118) 462 ($col - 132) 32 11 $Pale -Align 3 -VAlign 3)
  [void](New-Box $sl $c 498 $col 32 $Pale)
  [void](New-Text $sl "정밀도 실패" ($c + 14) 498 100 32 11 $Deep -Bold -VAlign 3)
  [void](New-Text $sl "분석 결과 ⊋ {구체값}" ($c + 118) 498 ($col - 132) 32 11 $Deep -Align 3 -VAlign 3)
  [void](New-Text $sl "찾아낸 공격 예시" $c 540 200 14 9.5 $Faint -Bold -Track 1.2)
  [void](New-Box $sl $c 558 $col 68 $Dark)
  [void](New-Text $sl "x = 1;`nwhile (-x) { x = 0; }`nx = x * x;" ($c + 18) 568 ($col - 36) 52 11 $OnDark -Font $MONO)
  [void](New-Text $sl "구체 실행  x = 0" $c 634 160 18 10.5 $Ink -Bold -Font $MONO)
  [void](New-Text $sl "분석 결과  x |-> [-inf, inf]" ($c + 160) 634 ($col - 160) 18 10.5 $Steel -Bold -Align 3 -Font $MONO)
  [void](New-Text $sl "guard가 x가 아니라 -x라 종료 후 필터가 약하고, x * x는 두 피연산자가 같은 변수라는 상관관계를 잃는다." $c 658 $col 36 10.5 $Body)
  [void](New-Text $sl "* 이전 자체 분석기 엔진에서 발견" $c 698 $col 16 9 $Faint)

  # ============================================================ BAND 2 — hero
  [void](New-Box $sl 0 758 $SW 272 $Mist)
  New-Section $sl $a 780 $CW "04" "잎에서 뿌리로, 작은 조각부터 쌓아 올린다"

  [void](New-Box $sl $a 830 210 106 $Dark)
  [void](New-Text $sl "int main() {`n  int x;`n  x = 1;`n  return x;`n}" ($a + 20) 840 170 88 11 $OnDark -Font $MONO)
  [void](New-Text $sl "EConst, LVar 같은 가장 작은 조각에서 시작해 뿌리까지 올라간다. 그림의 위에서 아래가 합성 순서다. 프로그램은 뿌리의 결론으로 따라 나온다." $a 946 264 62 11 $Body)

  $TX = 350; $TW = 430
  $cA = $TX + 92;  $wA = 186
  $cB = $TX + 322; $wB = 200
  $cRoot = $TX + $TW / 2
  $ty = 834; $dy = 21
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

  [void](New-Box $sl 812 830 326 76 $Paper $Rule 1)
  [void](New-Box $sl 812 830 4 76 $Deep)
  [void](New-Text $sl "크기 순서대로 pool에 쌓는다" 832 838 290 18 12 $Deep -Bold)
  [void](New-Text $sl "규칙마다 이미 만들어 둔 더 작은 조각만 꺼내 쓴다. 호출된 함수의 증명도 언제나 진부분나무이므로 재귀·상호재귀가 잘 정의된다." 832 858 290 42 10.5 $Body)
  [void](New-Box $sl 812 918 326 84 $Paper $Rule 1)
  [void](New-Box $sl 812 918 4 84 $Deep)
  [void](New-Text $sl "메모리가 항상 따라 붙는다" 832 926 290 18 12 $Deep -Bold)
  [void](New-Text $sl "완전한 프로그램은 스스로 메모리를 정하지만, 조각은 앞뒤 메모리의 관계만 안다. 메모리를 나중으로 미루면 정지 문제에 빠지므로, 조각을 만들 때 전후 메모리를 확정한다." 832 946 290 50 10.5 $Body)

  # ============================================================ BAND 3
  # -- 05 holes and unification
  New-Section $sl $a 1054 $col "05" "실행 안 된 자리는 hole로"
  [void](New-Box $sl $a 1104 230 100 $Dark)
  [void](New-Text $sl "if (x || ?H1) {`n  return 0;`n} else {`n  ?H2`n}" ($a + 20) 1114 190 82 11 $OnDark -Font $MONO)
  New-Chip $sl "?H1" $a 1216 44 22 $Deep $Paper 10 -1 $MONO
  [void](New-Text $sl "short-circuit로 평가되지 않은 오른쪽 피연산자 — ExpHole" ($a + 54) 1216 ($col - 54) 30 10.5 $Ink)
  New-Chip $sl "?H2" $a 1254 44 22 $Steel $Paper 10 -1 $MONO
  [void](New-Text $sl "선택되지 않은 branch, 또는 return · break · continue 뒤에 잘린 block 꼬리 — StmtSeqHole" ($a + 54) 1254 ($col - 54) 42 10.5 $Ink)
  [void](New-Box $sl $a 1304 $col 30 $Deep)
  [void](New-Text $sl "실행된 자리에는 hole이 남을 수 없다." ($a + 14) 1304 ($col - 28) 30 11 $Paper -Bold -VAlign 3)
  [void](New-Text $sl "같은 정적 위치가 loop · 재귀로 여러 번 실행되면 그 조각들이 서로 맞아야 한다. 타입 추론에서와 같은 unification으로 맞추고, 나무와 substitution을 따로 들고 다닌다." $a 1342 $col 46 10.5 $Body)

  # -- 06 fill the holes, then hand it to the analyser
  New-Section $sl $b 1054 $two "06" "hole을 채워 분석기에 넣는다"
  [void](New-Text $sl "hole 자리는 어차피 실행되지 않았다. 그래서 아무 코드나 채워 넣어도 이 증명나무가 말하는 실행 의미는 바뀌지 않는다. 문맥이 맞을 필요도 없다. 새로운 실행이 생기지 않도록 함수 호출만 넣지 않는다." $b 1104 $two 34 11.5 $Ink)
  New-Node $sl "완성된 holed 증명나무" "미실행 자리는 아직 hole" $b 1150 152 54 $Paper $Rule $Deep $Body 11.5
  [void](New-Rule $sl ($b + 156) 1177 ($b + 172) 1177 $Steel 1.4 -Arrow)
  New-Node $sl "hole 채우기" "아무 코드나 — 호출만 제외" ($b + 174) 1150 138 54 $Pale $Pale $Deep $Body 11.5
  [void](New-Rule $sl ($b + 316) 1177 ($b + 332) 1177 $Steel 1.4 -Arrow)
  New-Node $sl "구체 CIL-- 프로그램" "hole 없는 완성된 코드" ($b + 334) 1150 140 54 $Deep $Deep $Paper $Pale 11.5
  [void](New-Rule $sl ($b + 476) 1170 ($b + 494) 1146 $Steel 1.4 -Arrow)
  [void](New-Rule $sl ($b + 476) 1184 ($b + 494) 1208 $Steel 1.4 -Arrow)
  New-Node $sl "증명나무의 구체값" "실제 실행 의미" ($b + 496) 1122 130 46 $Paper $Rule $Deep $Body 11
  New-Node $sl "분석기의 분석 결과" "어림잡은 값" ($b + 496) 1186 130 46 $Paper $Rule $Deep $Body 11
  [void](New-Rule $sl ($b + 628) 1146 ($b + 646) 1170 $Steel 1.4 -Arrow)
  [void](New-Rule $sl ($b + 628) 1208 ($b + 646) 1184 $Steel 1.4 -Arrow)
  [void](New-Box $sl ($b + 646) 1150 68 54 $Deep)
  [void](New-Text $sl "비교" ($b + 646) 1150 68 54 12.5 $Paper -Bold -Align 2 -VAlign 3)
  [void](New-Box $sl $b 1240 350 30 $Deep)
  [void](New-Text $sl "구체값 ∉ 분석 결과   →   안전성 공격" ($b + 14) 1240 322 30 11 $Paper -Bold -VAlign 3)
  [void](New-Box $sl ($b + 364) 1240 350 30 $Pale)
  [void](New-Text $sl "분석 결과 ⊋ {구체값}   →   정밀도 공격" ($b + 378) 1240 322 30 11 $Deep -Bold -VAlign 3)
  [void](New-Text $sl "정밀도 공격은 튜링 완전한 부분집합이기만 하면 반드시 존재한다 (Rice's Theorem). 안전성 공격은 버그를 찾는 일이라, 언어 기능이 많을수록 유리하다." $b 1280 $two 32 10.5 $Body)

  # ============================================================ BAND 4
  New-Section $sl $a 1400 $CW "07" "정말 올바른 공격인가"
  [void](New-Text $sl "공격이 성공했다고 말하려면, 분석기가 전제하는 실행 의미와 우리가 CIL--에 준 실행 의미가 같아야 한다." $a 1450 $CW 22 13 $Ink -Bold)
  [void](New-Box $sl $a 1482 340 84 $Deep)
  [void](New-Text $sl "아무도 실행 의미를 엄밀히 적어두지 않았다" ($a + 18) 1490 304 18 11.5 $Paper -Bold)
  [void](New-Text $sl "C의 ISO 표준은 자연어로 되어 있고, CIL에도 엄밀한 실행 의미가 없다. 분석기 역시 sound in design이라고 말할 뿐 concrete semantics를 정의하지 않는다." ($a + 18) 1510 304 50 10 $Pale)
  [void](New-Text $sl "우리에게는 CIL--의 Big-Step 실행 의미가 있다. 비결정성이 남아 있으면 공격에 성공한 것처럼 보여도 사실은 비결정성 탓일 수 있으므로, 하나씩 없앤다." $a 1574 340 36 10.5 $Body)

  # -- nondeterminism table: what C leaves open, and where CIL-- closes it
  $tx = 412; $tw = 726
  $w1 = 156; $w2 = 186; $w3 = 178; $w4 = 206
  $x2 = $tx + $w1; $x3 = $x2 + $w2; $x4 = $x3 + $w3
  [void](New-Rule $sl $tx 1482 ($tx + $tw) 1482 $Deep 1.6)
  [void](New-Text $sl "예"     ($tx + 4) 1486 $w1 15 9 $Steel -Bold -Track 1)
  [void](New-Text $sl "C"      ($x2 + 4) 1486 $w2 15 9 $Steel -Bold -Track 1)
  [void](New-Text $sl "CIL"    ($x3 + 4) 1486 $w3 15 9 $Steel -Bold -Track 1)
  [void](New-Text $sl "CIL--"  ($x4 + 4) 1486 $w4 15 9 $Steel -Bold -Track 1)
  [void](New-Rule $sl $tx 1503 ($tx + $tw) 1503 $Deep 1)
  $rows = @(
    @("f() + g()",      "계산 순서가 정해지지 않음", "호출이 식에 들어가지 않음", "없앰"),
    @("i = i++ + 1;",   "undefined behavior",       "i++ 문법이 없음",          "없앰"),
    @("int x; use(x);", "indeterminate value",      "indeterminate value",      "합성 시 만들지 않음"),
    @("`"a`" == `"a`"", "true / false 모두 가능",   "여전히 비결정적",           "문자열이 없음"),
    @("char c = -1;",   "-1 또는 255",              "여전히 비결정적",           "char가 없음"),
    @("malloc(n)",      "주소가 비결정적",           "fresh object",             "포인터가 없음")
  )
  $ry = 1505
  foreach ($r in $rows) {
    [void](New-Text $sl $r[0] ($tx + 4) $ry $w1 15 9 $Ink -Bold -Font $MONO -VAlign 3)
    [void](New-Text $sl $r[1] ($x2 + 4) $ry $w2 15 9 $Body -VAlign 3)
    [void](New-Text $sl $r[2] ($x3 + 4) $ry $w3 15 9 $Body -VAlign 3)
    [void](New-Text $sl $r[3] ($x4 + 4) $ry $w4 15 9 $Deep -Bold -VAlign 3)
    [void](New-Rule $sl $tx ($ry + 17) ($tx + $tw) ($ry + 17) $Rule 0.75)
    $ry += 17
  }

  # ============================================================ COLOUR FOOT
  [void](New-Box $sl 0 1616 $SW 32 $Mist)
  [void](New-Rule $sl 0 1616 $SW 1616 $Rule 1)
  [void](New-Box $sl 0 1648 $SW ($SH - 1648) $Deep)

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
