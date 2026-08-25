$ErrorActionPreference = 'Stop'
$here     = Split-Path -Parent $MyInvocation.MyCommand.Path
$pptxPath = Join-Path $here 'SigPL_new.pptx'
$outPath  = Join-Path $here 'shapes_all.txt'

$ppt = New-Object -ComObject PowerPoint.Application
$deck = $ppt.Presentations.Open($pptxPath, $true, $false, $false)
$slide = $deck.Slides.Item(1)
$out = New-Object System.Collections.Generic.List[string]
$i = 0
foreach ($sh in $slide.Shapes) {
  $i++
  $type = $sh.Type
  $alt = ''
  try { $alt = $sh.AlternativeText } catch {}
  $txt = ''
  try {
    if ([int]$sh.HasTextFrame -eq -1) {
      $tr = $sh.TextFrame.TextRange
      if ($tr.Length -gt 0) { $txt = $tr.Text.Substring(0, [Math]::Min(60, $tr.Text.Length)) }
    }
  } catch {}
  $t = $txt -replace "`r","|" -replace "`n","|"
  $out.Add("[$i] type=$type L=$([int]$sh.Left) T=$([int]$sh.Top) W=$([int]$sh.Width) H=$([int]$sh.Height) alt='$alt' :: $t")
}
[System.IO.File]::WriteAllLines($outPath, $out, [System.Text.UTF8Encoding]::new($false))
$deck.Close(); $ppt.Quit()
Write-Host "wrote $outPath ($($out.Count) shapes)"
