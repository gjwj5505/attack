# SigPL_new.pptx 를 제자리에서 손본다 — 새로 그리지 않는다.
#   1) A2 -> A1 (594 x 841 mm) 로 판형 확대, 모든 도형/글자/선을 같은 비율로
#   2) 노랑(#E7A811) 제거. 파랑 3개로 통일:
#        Deep  #00397F  서울대 딥블루 — 헤더/푸터 밴드, 섹션 제목, 강조 박스
#        Mid   #3A72B8  섹션 번호, 액센트 바, 화살표, 칩, 작은 라벨
#        Light #A9C6E6  딥블루 위에 얹히는 글자와 헤더 실선
#      코드 블록의 syntax highlighting 색은 그대로 둔다.
#
# 이미 열려 있는 프레젠테이션이 있으면 그걸 그대로 고친다(저장 안 한 편집 보존).
#
# Usage:
#   powershell -ExecutionPolicy Bypass -File restyle_a1.ps1 -PptxPath <abs .pptx> `
#     [-BackupPath <abs .pptx>] [-PngPath <abs .png>] [-PdfPath <abs .pdf>]

param(
  [Parameter(Mandatory = $true)][string]$PptxPath,
  [string]$BackupPath = "",
  [string]$PngPath = "",
  [string]$PdfPath = ""
)

$ErrorActionPreference = "Stop"

function RGB([int]$r, [int]$g, [int]$b) { return $r + (256 * $g) + (65536 * $b) }

$Deep  = RGB 0   57  127
$Mid   = RGB 58  114 184
$Light = RGB 169 198 230

$Gold  = RGB 231 168 17     # 걷어낼 노랑
$Steel = RGB 71  106 173    # 예전 중간 파랑
$Blue2 = RGB 0   70  158    # 예전 푸터 밴드

# A1 portrait. 폭 기준으로 글자·선을 키워 줄바꿈이 그대로 유지되게 한다.
$A1W = 594 / 25.4 * 72
$A1H = 841 / 25.4 * 72

$mapped = 0

# 색 하나를 새 팔레트로 옮긴다. $OnDeep 면 딥블루 위에 놓인 요소라는 뜻이라
# 같은 노랑이라도 밝은 파랑으로 간다.
function Map-Color {
  param([int]$C, [bool]$OnDeep)
  if ($C -eq $Gold)  { if ($OnDeep) { return $Light } else { return $Mid } }
  if ($C -eq $Steel) { if ($OnDeep) { return $Light } else { return $Mid } }
  if ($C -eq $Blue2) { return $Deep }
  return $C
}

function Recolor-Shape {
  param($S, [bool]$OnDeep)
  if ($S.Fill.Visible -eq -1) {
    $n = Map-Color $S.Fill.ForeColor.RGB $OnDeep
    if ($n -ne $S.Fill.ForeColor.RGB) { $S.Fill.ForeColor.RGB = $n; $script:mapped++ }
  }
  if ($S.Line.Visible -eq -1) {
    $n = Map-Color $S.Line.ForeColor.RGB $OnDeep
    if ($n -ne $S.Line.ForeColor.RGB) { $S.Line.ForeColor.RGB = $n; $script:mapped++ }
  }
  if ($S.HasTextFrame -eq -1 -and $S.TextFrame2.HasText -eq -1) {
    $runs = $S.TextFrame2.TextRange.Runs()
    for ($r = 1; $r -le $runs.Count; $r++) {
      $f = $runs.Item($r).Font
      $n = Map-Color $f.Fill.ForeColor.RGB $OnDeep
      if ($n -ne $f.Fill.ForeColor.RGB) { $f.Fill.ForeColor.RGB = $n; $script:mapped++ }
    }
  }
}

function Scale-Shape {
  param($S, $Geo, [double]$Kx, [double]$Ky, [double]$Kf)
  try { $S.LockAspectRatio = 0 } catch {}
  $S.Left   = $Geo[0] * $Kx
  $S.Top    = $Geo[1] * $Ky
  $S.Width  = $Geo[2] * $Kx
  $S.Height = $Geo[3] * $Ky
  if ($S.Line.Visible -eq -1) { $S.Line.Weight = $S.Line.Weight * $Kf }
  if ($S.HasTextFrame -eq -1 -and $S.TextFrame2.HasText -eq -1) {
    $tf = $S.TextFrame2
    $tf.MarginLeft = $tf.MarginLeft * $Kx; $tf.MarginRight  = $tf.MarginRight  * $Kx
    $tf.MarginTop  = $tf.MarginTop  * $Ky; $tf.MarginBottom = $tf.MarginBottom * $Ky
    $paras = $tf.TextRange.Paragraphs()
    for ($p = 1; $p -le $paras.Count; $p++) {
      $pf = $paras.Item($p).ParagraphFormat
      if ($pf.SpaceAfter  -gt 0) { $pf.SpaceAfter  = $pf.SpaceAfter  * $Kf }
      if ($pf.SpaceBefore -gt 0) { $pf.SpaceBefore = $pf.SpaceBefore * $Kf }
    }
    $runs = $tf.TextRange.Runs()
    for ($r = 1; $r -le $runs.Count; $r++) {
      $f = $runs.Item($r).Font
      $f.Size = $f.Size * $Kf
      if ($f.Spacing -ne 0) { $f.Spacing = $f.Spacing * $Kf }
    }
  }
}

$ownedApp = $false; $app = $null; $pres = $null; $ownedPres = $false
try {
  try { $app = [Runtime.InteropServices.Marshal]::GetActiveObject("PowerPoint.Application") }
  catch { $app = New-Object -ComObject PowerPoint.Application; $ownedApp = $true }
  $app.Visible = -1

  $leaf = Split-Path $PptxPath -Leaf
  foreach ($p in $app.Presentations) { if ($p.Name -eq $leaf) { $pres = $p } }
  if ($null -eq $pres) { $pres = $app.Presentations.Open($PptxPath, 0, 0, -1); $ownedPres = $true }

  if ($BackupPath -ne "") {
    if (Test-Path $BackupPath) { Remove-Item $BackupPath -Force }
    $pres.SaveCopyAs($BackupPath, 24)
  }

  $sl = $pres.Slides.Item(1)
  $headerBottom = 196.0   # 딥블루 헤더 밴드의 아래끝 (확대 전 좌표)

  # --- 1) 색 -------------------------------------------------------------
  foreach ($s in $sl.Shapes) {
    $onDeep = ($s.Top -lt $headerBottom)
    Recolor-Shape $s $onDeep
  }

  # --- 2) 판형 -----------------------------------------------------------
  # 판형을 키우면 PowerPoint가 도형을 새 페이지 한가운데로 밀어 놓는다. 그래서
  # 확대 전 좌표를 먼저 찍어 두고, 그 값으로 다시 앉힌다.
  $kx = $A1W / $pres.PageSetup.SlideWidth
  $ky = $A1H / $pres.PageSetup.SlideHeight
  $kf = $kx
  $geo = @{}
  foreach ($s in $sl.Shapes) { $geo[$s.Id] = @($s.Left, $s.Top, $s.Width, $s.Height) }
  $pres.PageSetup.SlideWidth  = $A1W
  $pres.PageSetup.SlideHeight = $A1H
  foreach ($s in $sl.Shapes) { Scale-Shape $s $geo[$s.Id] $kx $ky $kf }

  $pres.Save()
  Write-Output ("recolored {0} attrs; scaled x{1:N4} to {2:N1} x {3:N1} pt" -f $mapped, $kx, $A1W, $A1H)

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
