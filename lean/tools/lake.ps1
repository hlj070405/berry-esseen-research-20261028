# 2026-10-28: use the pinned local Lean SDK without changing the user's PATH.
$ErrorActionPreference = 'Stop'
[Diagnostics.Process]::GetCurrentProcess().ProcessorAffinity = [IntPtr]3
$sdkBin = Join-Path $env:USERPROFILE '.cache/berry-esseen-tools/lean-4.35.0-windows/bin'
if (-not (Test-Path -LiteralPath (Join-Path $sdkBin 'lake.exe'))) {
    throw 'Run tools/bootstrap.py with Python and zstandard first.'
}
$env:PATH = $sdkBin + [IO.Path]::PathSeparator + $env:PATH
$env:MATHLIB_NO_CACHE_ON_UPDATE = '1'
$lakeArguments = @($args)
if ($lakeArguments.Count -ge 2 -and $lakeArguments[0] -eq 'env' -and
    $lakeArguments[1] -eq 'lean' -and
    -not ($lakeArguments | Where-Object { $_ -match '^(-j|--threads)' })) {
    $lakeArguments = @('env', 'lean', '-j', '2') + @($lakeArguments | Select-Object -Skip 2)
}
& (Join-Path $sdkBin 'lake.exe') @lakeArguments
exit $LASTEXITCODE
