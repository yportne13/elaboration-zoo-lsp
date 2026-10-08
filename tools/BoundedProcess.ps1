# tools/BoundedProcess.ps1 -- shared bounded-process runner for the tools here.
# ASCII only, on purpose (PowerShell 5.1 reads .ps1 as ANSI; see tools/README.md).
# Dot-source it:  . (Join-Path $PSScriptRoot "BoundedProcess.ps1")
#
# WHY NOT Start-Process -PassThru
#   In PowerShell 5.1 the object returned by
#       Start-Process ... -PassThru -RedirectStandardOutput x -RedirectStandardError y
#   does NOT expose a usable ExitCode: it reads back as an empty value even after
#   the process has exited. That silently breaks every caller that trusts it --
#   a passing suite whose tests all reported "ok" gets counted as a failure, and
#   a genuinely failed command can look fine. The .NET Process API used below
#   reports ExitCode reliably.
#
# WHAT ELSE THIS BUYS
#   * live WorkingSet64 polling, so callers can enforce a real memory ceiling on
#     an engine with no termination guard (round 1 saw a 13.8 GB l13bench);
#   * both streams decoded as UTF-8 (cargo output and l13bench's [diag] lines
#     are UTF-8; the console codepage would mojibake them);
#   * no window, no shell, so no cmd.exe quoting surprises.

# Build a Windows command line from an argument array.
function ConvertTo-ArgString {
    param([string[]]$Arguments)
    $parts = @()
    foreach ($a in $Arguments) {
        if ($null -eq $a) { continue }
        $s = [string]$a
        if ($s -eq "") { $parts += '""'; continue }
        if ($s -match '[\s"]') {
            $parts += '"' + ($s -replace '"', '\"') + '"'
        } else {
            $parts += $s
        }
    }
    return ($parts -join ' ')
}

# Run one process under a wall-clock timeout and an optional memory ceiling.
# Always reaps the child. Returns a plain object:
#   Exited     true only when the child finished on its own
#   ExitCode   the real exit code (null if it could not be read)
#   TimedOut   killed after TimeoutSec
#   MemLimit   true when MemExceeded tripped
#   MemExceeded  killed after MemLimitGB
#   PeakGB     highest working set observed while running
#   Secs       wall clock
#   Stdout/Stderr  decoded text
#   AllLines   Stdout+Stderr split into lines
#   StartError non-empty when the process could not even start
function Invoke-BoundedProcess {
    param(
        [Parameter(Mandatory = $true)][string]$FilePath,
        [string[]]$Arguments = @(),
        [string]$WorkingDirectory = "",
        [int]$TimeoutSec = 3600,
        [double]$MemLimitGB = 0,
        [int]$PollMs = 400
    )

    $blank = [pscustomobject]@{
        Exited = $false; ExitCode = $null; TimedOut = $false; MemExceeded = $false
        PeakGB = 0.0; Secs = 0.0; Stdout = ""; Stderr = ""; AllLines = @()
        StartError = ""
    }

    $psi = New-Object System.Diagnostics.ProcessStartInfo
    $psi.FileName = $FilePath
    $psi.Arguments = ConvertTo-ArgString -Arguments $Arguments
    if ($WorkingDirectory) { $psi.WorkingDirectory = $WorkingDirectory }
    $psi.UseShellExecute = $false
    $psi.RedirectStandardOutput = $true
    $psi.RedirectStandardError = $true
    $psi.StandardOutputEncoding = [System.Text.Encoding]::UTF8
    $psi.StandardErrorEncoding = [System.Text.Encoding]::UTF8
    $psi.CreateNoWindow = $true

    $proc = New-Object System.Diagnostics.Process
    $proc.StartInfo = $psi
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    try {
        $null = $proc.Start()
    } catch {
        $blank.StartError = $_.Exception.Message
        return $blank
    }
    $soTask = $proc.StandardOutput.ReadToEndAsync()
    $seTask = $proc.StandardError.ReadToEndAsync()

    $timedOut = $false
    $memExceeded = $false
    $peak = 0.0
    while (-not $proc.HasExited) {
        Start-Sleep -Milliseconds $PollMs
        try {
            $proc.Refresh()
            if (-not $proc.HasExited) {
                $wsGB = $proc.WorkingSet64 / 1GB
                if ($wsGB -gt $peak) { $peak = $wsGB }
                if ($MemLimitGB -gt 0 -and $wsGB -gt $MemLimitGB) { $memExceeded = $true; break }
            }
        } catch { }
        if ($sw.Elapsed.TotalSeconds -gt $TimeoutSec) { $timedOut = $true; break }
    }
    if ($timedOut -or $memExceeded) {
        try { $proc.Kill() } catch { }
    }
    try { $proc.WaitForExit() } catch { }
    $sw.Stop()

    $stdout = ""
    $stderr = ""
    try { $stdout = $soTask.Result } catch { }
    try { $stderr = $seTask.Result } catch { }
    $exit = $null
    try { $exit = $proc.ExitCode } catch { $exit = $null }

    return [pscustomobject]@{
        Exited = (-not $timedOut -and -not $memExceeded)
        ExitCode = $exit
        TimedOut = $timedOut
        MemExceeded = $memExceeded
        PeakGB = [math]::Round($peak, 2)
        Secs = [math]::Round($sw.Elapsed.TotalSeconds, 1)
        Stdout = $stdout
        Stderr = $stderr
        AllLines = @(($stdout + "`n" + $stderr) -split "`r?`n")
        StartError = ""
    }
}
