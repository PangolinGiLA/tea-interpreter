#!/bin/bash
DIR="$(dirname "$0")"
cd "$DIR"

if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <filename> (skip .brew extension)"
    echo "The file is divided into contents in all top-level curly brackets."
    echo "The original file is not changed."
    echo "Alternatively, use: $0 --clean to remove all files ending on non-0 digit and extension."
    exit 1
fi

if [ "$1" == "--clean" ]; then
    find . -maxdepth 1 -type f -regex '.*[1-9]\.tea$' -exec rm -f {} \;
    exit 0
fi


brew_tea() {
    brew_file=$1
    # Read the contents of the file
    content=$(< "$brew_file".brew)

    # Initialize variables
    level=0
    buffer=""
    rep=1

    # Iterate over each character in the content
    while IFS= read -r -N1 char; do
        if [[ "$char" == "{" ]]; then
            buffer+="$char"
            ((level++))
        elif [[ "$char" == "}" ]]; then
            ((level--))
            buffer+="$char"
            if [[ $level -eq 0 ]]; then
                # Print to the next file
                file="$brew_file$rep.tea"
                echo "$buffer" > $file
                # Reset the buffer and increment the file counter
                buffer=""
                ((rep++))
            fi
        else
            if [[ $level -gt 0 ]]; then
                buffer+="$char"
            fi
        fi
    done <<< "$content"
}

if [ "$1" == "all" ]; then
    for brew in *.brew; do
        brew=$(basename $brew .brew)
        brew_tea $brew
    done
    exit 0
fi

brew_tea $1