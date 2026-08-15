# Measure peak working set of a command invocation.
# Usage: powershell -File tools\measure_peak.ps1 <exe> <arg1> <arg2> ...
param(
    [Parameter(Mandatory = $true)][string]$Exe,
    [Parameter(ValueFromRemainingArguments = $true)][string[]]$Args
)
$outFile = Join-Path $env:TEMP "typort_peak_out.txt"
$errFile = Join-Path $env:TEMP "typort_peak_err.txt"
$p = Start-Process -FilePath $Exe -ArgumentList $Args -PassThru `
    -WindowStyle Hidden -RedirectStandardOutput $outFile -RedirectStandardError $errFile
$peak = 0
$peakVm = 0
try {
    while (-not $p.HasExited) {
        Start-Sleep -Milliseconds 100
        $p.Refresh()
        if ($p.WorkingSet64 -gt $peak) { $peak = $p.WorkingSet64 }
        if ($p.VirtualMemorySize64 -gt $peakVm) { $peakVm = $p.VirtualMemorySize64 }
    }
    $p.WaitForExit()
} catch {
    # process may have exited between checks; re-query
    try { $p.Refresh() } catch { }
}
$code = $null
try { $code = $p.ExitCode } catch { }
Write-Output ("PEAK_WS_MB={0:N1}" -f ($peak / 1MB))
Write-Output ("PEAK_VM_MB={0:N1}" -f ($peakVm / 1MB))
Write-Output ("EXIT_CODE={0}" -f $code)
