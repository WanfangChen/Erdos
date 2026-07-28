$ErrorActionPreference = "Stop"

$projectDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$localLake = Join-Path $env:USERPROFILE `
  ".elan\toolchains\leanprover--lean4---v4.27.0-rc1\bin\lake.exe"

if (-not (Test-Path -LiteralPath $localLake)) {
  throw "Pinned Lean 4.27.0-rc1 toolchain not found at $localLake"
}

Push-Location $projectDir
try {
  & $localLake build
  if ($LASTEXITCODE -ne 0) {
    throw "lake build failed"
  }

  & $localLake env lean "Erdos279/Audit.lean"
  if ($LASTEXITCODE -ne 0) {
    throw "axiom audit failed"
  }

  $sourceFiles = @(
    Get-Item -LiteralPath "Erdos279.lean"
    Get-ChildItem -LiteralPath "Erdos279" -Recurse -Filter "*.lean"
  )
  $forbidden = $sourceFiles |
    Select-String -Pattern "\bsorry\b|\badmit\b|sorryAx|^\s*axiom\b|^\s*opaque\b|^\s*unsafe\b"
  if ($forbidden) {
    $forbidden | ForEach-Object { Write-Error $_.Line }
    throw "forbidden proof placeholder found"
  }

  Write-Output "Verification complete: build and axiom audit passed."
}
finally {
  Pop-Location
}
