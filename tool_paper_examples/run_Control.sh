#!/bin/bash

echo "Moving into Control directory"
cd Control

echo "Creating synthesis file test-control.ucl"
echo 'uclidtool test-control.ucl -y "delphi" -g "delphi_file"'
time uclidtool test-control.ucl -y "delphi" -g "delphi_file"

echo "Running delphi on file"
delphi delphi_file.sl