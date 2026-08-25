# dump_text.ps1 — list every text-bearing shape in SigPL_new.pptx
# writes to shapes.txt so we can inspect actual marker wording.

$ErrorActionPreference = 'Stop'
$here     = Split-Path -Parent $MyInvocation.MyCommand.Path
$pptxPath = Join-Path $here 'SigPL_new.pptx'
$outPath  = Join-Path $here 'shapes.txt'

$ppt = New-Object -ComObject PowerPoint.Application
$deck = $ppt.Presentations.Open($pptxPath, $true, $false, $false)
$slide = $deck.Slides.Item(1)

$out = New-Object System.Collections.Generic.List[string]
$i = 0
foreach ($sh in $slide.Shapes) {
  $i++
  $txt = ''
  try {
    if ([int]$sh.HasTextFrame -eq -1) {
      $tr = $sh.TextFrame.TextRange
      if ($tr.Length -gt 0) { $txt = $tr.Text }
    }
  } catch { $txt = '<err:' + $_.Exception.Message + '>' }
  $t = $txt -replace "`r","|" -replace "`n","|" -replace "`v","|"
  if ($t -eq '') { $t = '<no text>' }
  $out.Add("[$i] L=$([int]$sh.Left) T=$([int]$sh.Top) W=$([int]$sh.Width) H=$([int]$sh.Height) :: $t")
}

[System.IO.File]::WriteAllLines($outPath, $out, [System.Text.UTF8Encoding]::new($false))

$deck.Close()
$ppt.Quit()
Write-Host "wrote $outPath ($($out.Count) shapes)"
