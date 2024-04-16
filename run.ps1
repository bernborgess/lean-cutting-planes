# Exit immediately if any command has a non-zero exit status.
$ErrorActionPreference = "Stop"

# Assuming 'lake build' is a command you can run on your system
& lake build

# Clear the console window
Clear-Host

# Run the compiled application
& .\.lake\build\bin\lean-cutting-planes
