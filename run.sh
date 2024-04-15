#!/bin/bash

# Exit immediately if any command has a non-zero exit status.
set -e

lake build

clear

./.lake/build/bin/lean-cutting-planes
