param([string]$LeanBin = '')

$ErrorActionPreference = 'Stop'
$originalPath = $env:PATH
try {
    if ($LeanBin) {
        $resolvedBin = (Resolve-Path -LiteralPath $LeanBin).Path
        $env:PATH = $resolvedBin + [IO.Path]::PathSeparator + $env:PATH
        $lakeCommand = Join-Path $resolvedBin 'lake.exe'
        $leanCommand = Join-Path $resolvedBin 'lean.exe'
    } else {
        $lakeCommand = (Get-Command lake -ErrorAction Stop).Source
        $leanCommand = (Get-Command lean -ErrorAction Stop).Source
    }
    Push-Location -LiteralPath $PSScriptRoot
    try {
        & $leanCommand --version
        if ($LASTEXITCODE -ne 0) { throw 'Lean version check failed.' }
        & $lakeCommand build
        if ($LASTEXITCODE -ne 0) { throw 'Lean build failed.' }
        $auditLines = @(& $lakeCommand env lean Audit.lean 2>&1)
        $auditExit = $LASTEXITCODE
        $auditLines | Write-Output
        if ($auditExit -ne 0) { throw 'Axiom audit did not compile.' }
        if (($auditLines -join "`n") -match 'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler') {
            throw 'Unexpected proof trust dependency detected.'
        }
        Write-Output 'PASS: library built; named theorem axiom audit passed.'
    } finally {
        Pop-Location
    }
} finally {
    $env:PATH = $originalPath
}
