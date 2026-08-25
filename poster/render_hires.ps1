# Export SigPL_new.pptx slide 1 as a hi-res PNG for review.
$ErrorActionPreference = 'Stop'
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
$pptx = Join-Path $here 'SigPL_new.pptx'
$png  = Join-Path $here 'SigPL_new_hires.png'

$ppt = New-Object -ComObject PowerPoint.Application
$deck = $ppt.Presentations.Open($pptx, $true, $false, $false)
$slide = $deck.Slides.Item(1)
$slide.Export($png, 'PNG', 2800, 3964)
$deck.Close(); $ppt.Quit()
Write-Host "exported $png"
