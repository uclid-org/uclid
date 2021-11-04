#!/bin/bash

echo "Moving into Control directory"
cd Control

echo "Creating synthesis file test-control.ucl"
echo 'uclid test-control.ucl -y "delphi" -g "delphi_file"'
uclid test-control.ucl -y "delphi" -g "delphi_file"

echo "Running delphi on file ..."
time delphi delphi_file.sl