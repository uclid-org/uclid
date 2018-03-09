#! /bin/bash
# run make when the files change
while true; do
    make
    echo "Waiting for files to be updated ..."
    inotifywait -e modify *.tex ../examples/tutorial/*
done

