# SigPL_new.pptx 의 본문만 새 6개 주제로 갈아끼운다 (A1 좌표 기준).
#
# 헤더 / 리드 문장 / 푸터는 손대지 않는다. 세로 위치가 $BodyTop~$BodyBot 사이인
# 도형만 지우고 다시 그리므로, 여러 번 돌려도 헤더·푸터는 그대로 남는다.
#
# 팔레트는 파랑 3개 + 중립 tint. 코드 블록만 기존 syntax highlighting 유지.
#
# Usage:
#   powershell -ExecutionPolicy Bypass -File build_body_v2.ps1 -PptxPath <abs .pptx> `
#     [-PngPath <abs .png>] [-PdfPath <abs .pdf>]

param(
  [Parameter(Mandatory = $true)][string]$PptxPath,
  [string]$PngPath = "",
  [string]$PdfPath = ""
)

$ErrorActionPreference = "Stop"

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
$Paper  = RGB 255 255 255
$Dark   = RGB 46  52  64
$OnDark = RGB 216 222 233
$CodeKw = RGB 136 192 208
$CodeNo = RGB 235 203 139

$SANS = "Aptos"
$MONO = "Consolas"

$BodyTop = 440.0
$BodyBot = 2200.0

function New-Box {
  param($Sl, [double]$X, [double]$Y, [double]$W, [double]$H,
        [int]$Fill = -1, [int]$Stroke = -1, [double]$Weight = 1)
  $s = $Sl.Shapes.AddShape(1, $X, $Y, $W, $H)
  if ($Fill -lt 0) { $s.Fill.Visible = 0 } else { $s.Fill.Solid(); $s.Fill.ForeColor.RGB = $Fill }
  if ($Stroke -lt 0) { $s.Line.Visible = 0 }
  else { $s.Line.Visible = -1; $s.Line.ForeColor.RGB = $Stroke; $s.Line.Weight = $Weight }
  return $s
}

function New-RBox {
  param($Sl, [double]$X, [double]$Y, [double]$W, [double]$H,
        [int]$Fill = -1, [int]$Stroke = -1, [double]$Weight = 1.2, [double]$R = 11)
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
        [int]$Color, [double]$Weight = 1.4, [switch]$Arrow)
  $l = $Sl.Shapes.AddLine($X1, $Y1, $X2, $Y2)
  $l.Line.ForeColor.RGB = $Color; $l.Line.Weight = $Weight
  if ($Arrow) { $l.Line.EndArrowheadStyle = 3; $l.Line.EndArrowheadLength = 2; $l.Line.EndArrowheadWidth = 2 }
  return $l
}

# 전문용어는 쉬운 우리말로 쓰고 원문 영어를 옆에 작게 붙인다. 본문 문자열에
# 그 영어를 [[...]] 로 표시해 두면 여기서 자동으로 작고 흐리게 조판된다.
function Split-Gloss {
  param([string]$Text)
  $plain = ""; $ranges = @(); $i = 0
  while ($i -lt $Text.Length) {
    $j = $Text.IndexOf("[[", $i)
    if ($j -lt 0) { $plain += $Text.Substring($i); break }
    $plain += $Text.Substring($i, $j - $i)
    $k = $Text.IndexOf("]]", $j)
    $g = $Text.Substring($j + 2, $k - $j - 2).Replace(" ", [char]0x00A0)
    if ($plain.Length -gt 0) {
      $last = $plain.Substring($plain.Length - 1, 1)
      if ($last -ne " " -and $last -ne "`n") { $plain += " " }
    }
    $ranges += ,@(($plain.Length + 1), $g.Length)
    $plain += $g
    $i = $k + 2
  }
  return @($plain, $ranges)
}

function New-Text {
  param($Sl, [string]$Text, [double]$X, [double]$Y, [double]$W, [double]$H,
        [double]$Size, [int]$Color, [switch]$Bold,
        [int]$Align = 1, [int]$VAlign = 1, [string]$Font = $SANS,
        [double]$Space = 0.95, [double]$Track = 0, [int]$Gloss = -1)
  $s = $Sl.Shapes.AddTextbox(1, $X, $Y, $W, $H)
  $tf = $s.TextFrame2
  $tf.AutoSize = 0; $tf.WordWrap = -1
  $tf.MarginLeft = 0; $tf.MarginRight = 0; $tf.MarginTop = 0; $tf.MarginBottom = 0
  $tf.VerticalAnchor = $VAlign
  $split = Split-Gloss $Text
  $tf.TextRange.Text = $split[0]
  $tr = $tf.TextRange
  $tr.Font.Name = $Font
  $tr.Font.NameFarEast = "맑은 고딕"
  $tr.Font.Size = $Size
  $tr.Font.Bold = if ($Bold) { -1 } else { 0 }
  $tr.Font.Fill.ForeColor.RGB = $Color
  if ($Track -ne 0) { $tr.Font.Spacing = $Track }
  $tr.ParagraphFormat.Alignment = $Align
  $tr.ParagraphFormat.SpaceWithin = $Space
  if ($split[1].Count -gt 0) {
    $gc = $Gloss
    if ($gc -lt 0) { if ($Color -eq $Paper) { $gc = $Light } else { $gc = $Faint } }
    foreach ($r in $split[1]) {
      $c = $tr.Characters($r[0], $r[1])
      $c.Font.Size = $Size * 0.68
      $c.Font.Bold = 0
      $c.Font.Fill.ForeColor.RGB = $gc
    }
  }
  $s.Left = $X; $s.Top = $Y; $s.Width = $W; $s.Height = $H
  return $s
}

function New-Bullets {
  param($Sl, [string[]]$Items, [double]$X, [double]$Y, [double]$W, [double]$H,
        [double]$Size, [int]$Color, [double]$After = 7)
  $t = ($Items | ForEach-Object { "·  $_" }) -join "`n"
  $s = New-Text $Sl $t $X $Y $W $H $Size $Color -Space 1.0
  $s.TextFrame2.TextRange.ParagraphFormat.SpaceAfter = $After
  return $s
}

# 어두운 코드판. 키워드·리터럴·구멍에만 색을 준다.
function New-Code {
  param($Sl, [string]$Text, [double]$X, [double]$Y, [double]$W, [double]$H,
        [double]$Size = 15, [double]$PadX = 28, [double]$PadY = 18)
  [void](New-RBox $Sl $X $Y $W $H $Dark -R 10)
  $s = New-Text $Sl $Text ($X + $PadX) ($Y + $PadY) ($W - 2 * $PadX) ($H - 2 * $PadY) $Size $OnDark -Font $MONO -Space 1.15
  $tr = $s.TextFrame2.TextRange
  foreach ($m in [regex]::Matches($Text, '\b(int|unsigned|while|if|else|return|void|loop|break|continue)\b')) {
    $tr.Characters($m.Index + 1, $m.Length).Font.Fill.ForeColor.RGB = $CodeKw
  }
  foreach ($m in [regex]::Matches($Text, '\b\d+\b|\?H\d')) {
    $tr.Characters($m.Index + 1, $m.Length).Font.Fill.ForeColor.RGB = $CodeNo
  }
  return $s
}

function New-Section {
  param($Sl, [double]$X, [double]$Y, [double]$W, [string]$No, [string]$Title, [double]$Size = 35)
  [void](New-Text $Sl $No $X $Y 62 48 $Size $Mid -Bold -VAlign 3)
  [void](New-Text $Sl $Title ($X + 70) $Y ($W - 70) 48 $Size $Deep -Bold -VAlign 3)
}

function New-Chip {
  param($Sl, [string]$Text, [double]$X, [double]$Y, [double]$W, [double]$H,
        [int]$Fill, [int]$Color, [double]$Size = 15, [int]$Stroke = -1, [string]$Font = $SANS)
  [void](New-RBox $Sl $X $Y $W $H $Fill $Stroke 1.2 -R 9)
  [void](New-Text $Sl $Text $X $Y $W $H $Size $Color -Bold -Align 2 -VAlign 3 -Font $Font)
}

function New-Node {
  param($Sl, [string]$Title, [string]$Sub, [double]$X, [double]$Y, [double]$W, [double]$H,
        [int]$Fill, [int]$Stroke, [int]$TitleColor, [int]$SubColor, [double]$TSize = 16)
  [void](New-RBox $Sl $X $Y $W $H $Fill $Stroke 1.2 -R 11)
  [void](New-Text $Sl $Title ($X + 8) ($Y + 11) ($W - 16) 24 $TSize $TitleColor -Bold -Align 2)
  [void](New-Text $Sl $Sub ($X + 10) ($Y + 36) ($W - 20) ($H - 42) 13 $SubColor -Align 2)
}

# 좌측 액센트 바가 달린 흰 카드
function New-Card {
  param($Sl, [string]$Title, [string]$Text, [double]$X, [double]$Y, [double]$W, [double]$H,
        [double]$TSize = 17, [double]$BSize = 14)
  [void](New-RBox $Sl $X $Y $W $H $Paper $Rule 1.2 -R 11)
  [void](New-Box $Sl $X ($Y + 17) 6 ($H - 34) $Mid)
  [void](New-Text $Sl $Title ($X + 28) ($Y + 15) ($W - 44) 26 $TSize $Deep -Bold)
  [void](New-Text $Sl $Text ($X + 28) ($Y + 46) ($W - 48) ($H - 60) $BSize $Body)
}

# 수식 기호 한 글자만 수학 글꼴로 바꿔 끼운다.
function Set-MathGlyph {
  param($Shape, [string]$Text, [char]$Ch, [double]$Size)
  $i = $Text.IndexOf($Ch)
  if ($i -lt 0) { return }
  $c = $Shape.TextFrame2.TextRange.Characters($i + 1, 1)
  $c.Font.Name = "Cambria Math"
  $c.Font.NameFarEast = "Cambria Math"
  $c.Font.Size = $Size
}

function New-Judg {
  param($Sl, [string]$Text, [double]$Cx, [double]$Y, [double]$BarW,
        [int]$BarColor, [int]$TextColor, [double]$Size = 13, [double]$BarWeight = 1.2)
  [void](New-Rule $Sl ($Cx - $BarW / 2) $Y ($Cx + $BarW / 2) $Y $BarColor $BarWeight)
  [void](New-Text $Sl $Text ($Cx - ($BarW + 90) / 2) ($Y + 3) ($BarW + 90) 24 $Size $TextColor -Align 2 -Font $MONO)
}

$ownedApp = $false; $app = $null; $pres = $null; $ownedPres = $false
try {
  try { $app = [Runtime.InteropServices.Marshal]::GetActiveObject("PowerPoint.Application") }
  catch { $app = New-Object -ComObject PowerPoint.Application; $ownedApp = $true }
  $app.Visible = -1

  $leaf = Split-Path $PptxPath -Leaf
  foreach ($p in $app.Presentations) { if ($p.Name -eq $leaf) { $pres = $p } }
  if ($null -eq $pres) { $pres = $app.Presentations.Open($PptxPath, 0, 0, -1); $ownedPres = $true }

  $sl = $pres.Slides.Item(1)

  # 본문 영역만 비운다. 헤더 · 리드 문장 · 푸터는 그대로 둔다.
  $doomed = @()
  foreach ($s in $sl.Shapes) { if ($s.Top -ge $BodyTop -and $s.Top -le $BodyBot) { $doomed += $s.Id } }
  foreach ($id in $doomed) {
    foreach ($s in $sl.Shapes) { if ($s.Id -eq $id) { $s.Delete(); break } }
  }
  Write-Output ("cleared {0} body shapes" -f $doomed.Count)

  $L = 74.0; $R = 869.0; $CW = 741.0

  # =====================================================================
  # ROW 1 — 01 분석기 공격이란 / 02 분석기 개발 사이클
  # =====================================================================
  New-Section $sl $L 452 $CW "01" "분석기 공격이란"
  [void](New-Text $sl "라이스 정리[[Rice's Theorem]] 때문에 분석기는 안전성 · 유한성 · 정밀도 셋 중 하나는 반드시 포기한다." $L 512 $CW 60 19 $Ink -Bold)

  $tw = ($CW - 32) / 3
  New-Node $sl "안전성" "soundness · 실제 값을 빠뜨리지 않음"  $L                  580 $tw 70 $Paper $Rule $Deep  $Body 17
  New-Node $sl "유한성" "termination · 언젠가 멈춤"            ($L + $tw + 16)     580 $tw 70 $Paper $Rule $Deep  $Body 17
  New-Node $sl "정밀도" "completeness · 쓸데없이 넓힘"         ($L + 2 * $tw + 32) 580 $tw 70 $Paper $Rule $Deep  $Body 17
  [void](New-Text $sl "셋 다 만족하는 분석기는 없다. 우리는 앞의 둘을 지키는 분석기를 공격한다." $L 660 $CW 24 14 $Faint)

  [void](New-Text $sl "그러면 남는 것은 정밀도 하나다. 그것이 어느 지점에서 깨지는지를 사람 없이 자동으로 찾아내는 일이 곧 공격이다." $L 694 $CW 52 15 $Body)
  [void](New-RBox $sl $L 754 $CW 46 $Lav -R 10)
  [void](New-Text $sl "요약 결과가 모든 값[[top = (-inf, +inf)]]으로 무너지는 지점이 가장 좋은 공격" ($L + 24) 754 ($CW - 48) 46 16 $Deep -Bold -VAlign 3)

  [void](New-Code $sl "x = 1;`nwhile (-x) { x = 0; }`nx = x * x;" $L 816 $CW 96 15)
  [void](New-Text $sl "구체 실행  x = 0" $L 922 340 26 15 $Ink -Bold -Font $MONO)
  [void](New-Text $sl "분석 결과  x |-> [-inf, inf] = top" ($L + 340) 922 ($CW - 340) 26 15 $Mid -Bold -Align 3 -Font $MONO)
  [void](New-Text $sl "조건식[[guard]]이 x가 아니라 -x라 끝난 뒤 걸러내기가 약하고, x * x는 두 항[[operand]]이 같은 변수라는 관계를 잃는다. 이전 자체 분석기 엔진에서 찾은 예다." $L 956 $CW 48 13.5 $Body)

  New-Section $sl $R 452 $CW "02" "분석기 개발 사이클"
  [void](New-Text $sl "공격은 개발 사이클의 한 단계다. 찾아낸 공격이 다음 분석기의 설계로 되먹임된다." $R 512 $CW 60 19 $Ink -Bold)

  [void](New-RBox $sl $R 584 $CW 196 $Mist $Rule 1.2 -R 16)
  $cx = @(885.0, 1071.0, 1257.0, 1443.0)
  New-Node $sl "디자인" "무엇을 어떻게 어림잡을지"   $cx[0] 612 150 66 $Paper $Rule $Deep $Body 16
  New-Node $sl "개발"   "실제로 구현"               $cx[1] 612 150 66 $Paper $Rule $Deep $Body 16
  New-Node $sl "증명"   "안전함[[sound]]을 보임"     $cx[2] 612 150 66 $Paper $Rule $Deep $Body 16
  New-Node $sl "공격"   "정밀도가 깨지는 곳"        $cx[3] 612 150 66 $Deep  $Deep $Paper $Light 16
  for ($i = 0; $i -lt 3; $i++) {
    [void](New-Rule $sl ($cx[$i] + 158) 645 ($cx[$i] + 178) 645 $Mid 1.8 -Arrow)
  }
  [void](New-Rule $sl 1518 678 1518 716 $Mid 1.8)
  [void](New-Rule $sl 1518 716 960 716 $Mid 1.8)
  [void](New-Rule $sl 960 716 960 678 $Mid 1.8 -Arrow)
  [void](New-Text $sl "찾아낸 공격을 다시 설계로" $R 726 $CW 24 14 $Mid -Bold -Align 2)

  [void](New-Text $sl "사람들이 실제로 많이 쓰는 코드 패턴에서 공격이 나오면, 그 공격은 더 좋은 분석기를 디자인하는 데 곧바로 기여한다." $R 802 $CW 52 15 $Body)
  [void](New-RBox $sl $R 866 $CW 46 $Lav -R 10)
  [void](New-Text $sl "억지스러운 코드보다, 흔한 코드 패턴에서 나온 공격이 값지다" ($R + 24) 866 ($CW - 48) 46 16 $Deep -Bold -VAlign 3)
  [void](New-Text $sl "공격에서 디자인으로 돌아오는 고리가 닫혀야, 분석기가 실제로 좋아진다." $R 928 $CW 40 13.5 $Faint)

  # =====================================================================
  # ROW 2 — 03 공격의 정의 / 04 증명나무를 합성하는 이유
  # =====================================================================
  New-Section $sl $L 1016 $CW "03" "공격의 정의"
  [void](New-Text $sl "프로그램 하나에 실행이 여러 갈래로 갈리는 성질[[nondeterminism]]을 없애야, 증명나무[[proof tree]]가 하나로 정해지고 정밀도를 따지는 일이 뜻을 가진다." $L 1076 $CW 64 19 $Ink -Bold)

  [void](New-RBox $sl $L 1152 $CW 100 $Lav -R 12)
  [void](New-Text $sl "CIL--   ·   C 스타일 시키는 대로 도는[[imperative]] 언어" ($L + 26) 1166 ($CW - 52) 26 18 $Deep -Bold)
  [void](New-Text $sl "대입 · 조건 · 반복 · 함수 호출(제 자신 부르기[[recursion]] 포함)은 갖추되, 계산 순서나 정해두지 않은 동작[[undefined behavior]] 같은 갈래는 문법에서 아예 잘라냈다." ($L + 26) 1196 ($CW - 52) 50 14 $Deep)

  [void](New-Text $sl "이런 갈래가 남아 있으면 한 프로그램에 실행이 여러 개 대응된다. 그러면 공격에 성공한 것처럼 보여도 사실은 그 갈래 탓일 수 있다." $L 1264 $CW 52 15 $Body)
  [void](New-Text $sl "갈래를 없애면, 프로그램 하나에 증명나무가 딱 하나로 정해진다." $L 1324 $CW 30 16 $Ink -Bold)

  [void](New-RBox $sl $L 1362 $CW 84 $Lav -R 12)
  $formula = "∃  지점 L, 변수 x.    분석 결과(L, x)  ⊋  실제 실행 의미(L, x)"
  $fs = New-Text $sl $formula $L 1372 $CW 34 19 $Deep -Bold -Align 2
  Set-MathGlyph $fs $formula ([char]0x2203) 22
  Set-MathGlyph $fs $formula ([char]0x228B) 24
  [void](New-Text $sl "어떤 프로그램 지점[[label]]과 변수에서, 요약된 결과가 실제 실행 의미보다 진짜로 더 크다[[strictly greater]]" $L 1406 $CW 24 13.5 $Faint -Align 2)
  [void](New-Text $sl "진짜로 더 크다 = 어림잡은 값 안에, 실제로는 절대 나올 수 없는 값이 섞여 있다." $L 1458 $CW 40 13.5 $Body)

  New-Section $sl $R 1016 $CW "04" "증명나무를 합성하는 이유"
  [void](New-Text $sl "프로그램을 먼저 지어내면[[synthesis]], 그것이 공격에 성공했는지 판정할 수 없다." $R 1076 $CW 64 19 $Ink -Bold)

  [void](New-Text $sl "공격 성공을 판정하려면 그 프로그램의 실제 실행 의미[[concrete semantics]]를 알아야 한다. 그런데 프로그램이 멈추는지조차 미리 알 수 없다 (라이스 정리). 쉽게 말해, 무한히 돌지도 모른다." $R 1152 $CW 64 15 $Body)

  [void](New-RBox $sl $R 1228 $CW 220 $Mist $Rule 1.2 -R 16)
  [void](New-Text $sl "프로그램을 먼저 — 안 되는 길" ($R + 24) 1244 400 22 14 $Faint -Bold -Track 1.5)
  New-Node $sl "프로그램 지어내기" "코드를 먼저 만든다"   889  1270 210 58 $Paper $Rule $Faint $Faint 15
  [void](New-Rule $sl 1103 1299 1125 1299 $Faint 1.6 -Arrow)
  New-Node $sl "실행해 보기"       "실행 의미를 확인"     1129 1270 210 58 $Paper $Rule $Faint $Faint 15
  [void](New-Rule $sl 1343 1299 1365 1299 $Faint 1.6 -Arrow)
  New-Node $sl "멈추는지 모른다"   "판정 불가"            1369 1270 221 58 $Paper $Rule $Faint $Faint 15
  [void](New-Rule $sl ($R + 24) 1342 ($R + $CW - 24) 1342 $Rule 1)
  [void](New-Text $sl "증명나무를 먼저 — 되는 길" ($R + 24) 1352 400 22 14 $Deep -Bold -Track 1.5)
  New-Node $sl "증명나무 지어내기" "실행 의미를 먼저"     889  1378 210 58 $Lav $Mid $Deep $Body 15
  [void](New-Rule $sl 1103 1407 1125 1407 $Mid 1.8 -Arrow)
  New-Node $sl "뿌리의 결론"       "프로그램은 따라 나옴" 1129 1378 210 58 $Lav $Mid $Deep $Body 15
  [void](New-Rule $sl 1343 1407 1365 1407 $Mid 1.8 -Arrow)
  New-Node $sl "실행이 존재한다"   "판정 가능"            1369 1378 221 58 $Lav $Mid $Deep $Body 15

  [void](New-Text $sl "유한한 증명나무가 있다는 것은, 곧 그 실행이 존재한다는 뜻이다." $R 1466 $CW 34 17 $Ink -Bold)

  # =====================================================================
  # ROW 3 — 05 증명나무의 크기 / 06 구멍 뚫린 증명나무와 짝맞추기
  # =====================================================================
  New-Section $sl $L 1540 $CW "05" "증명나무의 크기"
  [void](New-Text $sl "잎에서 뿌리로[[bottom-up]] 빠짐없이 지어 올리려면, '크기'를 무엇으로 잡을지가 핵심이다." $L 1600 $CW 60 19 $Ink -Bold)

  [void](New-RBox $sl $L 1672 $CW 252 $Mist $Rule 1.2 -R 16)
  $TX = 115.0; $TW = 650.0
  $cA = $TX + 139; $wA = 281
  $cB = $TX + 487; $wB = 302
  $cRoot = $TX + $TW / 2
  $ty = 1706.0; $dy = 30.0
  foreach ($ax in @(($cA - 139), ($cA + 9), ($cB - 70))) {
    [void](New-Rule $sl $ax ($ty - 6) ($ax + 133) ($ty - 6) $Rule 1)
  }
  [void](New-Text $sl "[LVar] x => s0+0" ($cA - 139) $ty 133 22 13 $Body -Align 2 -Font $MONO)
  [void](New-Text $sl "[EConst] 1 => 1"  ($cA + 9)   $ty 133 22 13 $Body -Align 2 -Font $MONO)
  [void](New-Text $sl "[LVar] x => s0+0" ($cB - 70)  $ty 133 22 13 $Body -Align 2 -Font $MONO)
  New-Judg $sl "[ISet] x = 1; => {x |-> 1}"           $cA    ($ty + $dy)      $wA $Rule $Ink
  New-Judg $sl "[ELval] x => 1"                       $cB    ($ty + $dy)      $wB $Rule $Ink
  New-Judg $sl "[SInstr] instr[1] => Normal"          $cA    ($ty + 2 * $dy)  $wA $Rule $Ink
  New-Judg $sl "[SReturnSome] return x; => Return(1)" $cB    ($ty + 2 * $dy)  $wB $Rule $Ink
  New-Judg $sl "[BSeq] block[2] => Return(1)"         $cRoot ($ty + 3 * $dy)  $TW $Rule $Ink
  New-Judg $sl "[FReturn] main() => Return(1)"        $cRoot ($ty + 4 * $dy)  $TW $Rule $Ink
  New-Judg $sl "[PMainReturn] main() => 1"            $cRoot ($ty + 5 * $dy)  $TW $Deep $Deep 14 2.6
  [void](New-Rule $sl $TX ($ty + 6 * $dy) ($TX + $TW) ($ty + 6 * $dy) $Deep 2.6)
  [void](New-Text $sl "잎에서 뿌리로 — proof_size(t) = 1 + sum of premise sizes" $TX ($ty + 6 * $dy + 8) $TW 24 13 $Faint -Align 2 -Font $MONO)

  New-Card $sl "마디 수[[node]]만 세면?" "실행되지 않는 갈림길[[branch]]에 아무리 큰 코드가 들어가도 증명나무는 커지지 않는다. 같은 크기의 나무에 대응하는 프로그램이 무한히 많아진다." $L 1944 360 152
  New-Card $sl "프로그램 크기로 재면?" "반대로 프로그램 크기는 그대로인데 실행 의미가 무한히 길어질 수 있다. 반복문 하나로 증명나무만 끝없이 자란다." 454 1944 361 152
  [void](New-Text $sl "어느 쪽도 혼자서는 안 된다. 문법에 '구멍'[[hole]]을 들이는 이유다." $L 2112 $CW 34 17 $Ink -Bold)

  New-Section $sl $R 1540 $CW "06" "구멍 뚫린 증명나무와 짝맞추기"
  [void](New-Text $sl "실행되지 않은 자리를 구멍[[hole]]으로 남기면, 크기를 그냥 마디 수로 정의할 수 있다." $R 1600 $CW 60 19 $Ink -Bold)

  [void](New-Code $sl "if (x || ?H1) {`n  return 0;`n} else {`n  ?H2`n}" $R 1672 420 152 15)
  New-Chip $sl "?H1" 1310 1684 62 32 $Mid $Paper 14 -1 $MONO
  [void](New-Text $sl "앞에서 이미 결판나 계산하지 않은 오른쪽 항" 1384 1684 226 46 13.5 $Ink)
  New-Chip $sl "?H2" 1310 1756 62 32 $Light $Deep 14 -1 $MONO
  [void](New-Text $sl "선택되지 않은 갈림길, 또는 return 뒤에 잘린 문장 꼬리" 1384 1756 226 62 13.5 $Ink)

  [void](New-Text $sl "구멍이 놓일 수 있는 자리 — 이 셋뿐" $R 1842 $CW 22 13.5 $Mid -Bold -Track 1.5)
  [void](New-Bullets $sl @("if 문의 선택되지 않은 갈림길[[branch]]",
                           "차례로 이어진 문장[[sequence]]의 맨 끝 — return · break · continue 뒤",
                           "&& / || 에서 앞에서 결판나[[short-circuit]] 계산하지 않은 오른쪽 항") $R 1868 $CW 90 14.5 $Ink 6)
  [void](New-RBox $sl $R 1966 $CW 46 $Lav -R 10)
  [void](New-Text $sl "올바른 증명나무에서 구멍은 절대 실행되지 않는다" ($R + 24) 1966 ($CW - 48) 46 16 $Deep -Bold -VAlign 3)

  [void](New-Text $sl "짝맞추기[[unification]] — 왜 필요한가" $R 2032 $CW 22 13.5 $Mid -Bold -Track 1.5)
  [void](New-Text $sl "반복문과 제 자신을 부르는 함수에서는 같은 자리가 여러 번 실행된다. 그때 나온 조각들은 서로 실제로 같아야 한다. 타입 추론[[type inference]]에서 쓰는 것과 같은 짝맞추기로 맞추고, 나무와 갈아끼우기[[substitution]]를 따로 들고 다닌다." $R 2058 $CW 84 14.5 $Body)

  $pres.Save()
  if ($PngPath -ne "") {
    if (Test-Path $PngPath) { Remove-Item $PngPath -Force }
    $sl.Export($PngPath, "PNG", 1400, 1982)
  }
  if ($PdfPath -ne "") {
    if (Test-Path $PdfPath) { Remove-Item $PdfPath -Force }
    $pres.SaveCopyAs($PdfPath, 32)
  }
  if ($ownedPres) { $pres.Close(); $pres = $null }
  Write-Output "OK $PptxPath"
} finally {
  if ($ownedPres -and $null -ne $pres) { try { $pres.Close() } catch {} }
  if ($ownedApp -and $null -ne $app) { try { $app.Quit() } catch {} }
  if ($null -ne $app) { try { [void][Runtime.InteropServices.Marshal]::ReleaseComObject($app) } catch {} }
  [GC]::Collect(); [GC]::WaitForPendingFinalizers()
}
