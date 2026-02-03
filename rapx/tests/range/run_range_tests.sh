#!/bin/bash

# RAP root directory
RAP_ROOT="/home/lcc/rust/RAP"
TESTS_DIR="$RAP_ROOT/rapx/tests/range"

if [ ! -d "$TESTS_DIR" ]; then
    echo "Error: Directory $TESTS_DIR does not exist."
    exit 1
fi

# Get subdirectories
subdirs=($(find "$TESTS_DIR" -maxdepth 1 -type d | grep -v "^$TESTS_DIR$" | sort))

if [ ${#subdirs[@]} -eq 0 ]; then
    echo "No subdirectories found in $TESTS_DIR."
    exit 1
fi

# Ask for RAP_LOG level once
echo "Select RAP_LOG level:"
echo "1. INFO (default)"
echo "2. DEBUG"
echo "3. TRACE"
echo "4. WARN"
read -p "Enter choice [1-4]: " log_choice

case $log_choice in
    2) export RAP_LOG=DEBUG ;;
    3) export RAP_LOG=TRACE ;;
    4) export RAP_LOG=WARN ;;
    *) export RAP_LOG=INFO ;;
esac

echo "RAP_LOG set to $RAP_LOG"

while true; do
    echo -e "\nAvailable range tests:"
    for i in "${!subdirs[@]}"; do
        echo "$((i+1)). $(basename "${subdirs[$i]}")"
    done
    echo "0. Exit"

    read -p "Select a test to run (0-${#subdirs[@]}): " choice

    if ! [[ "$choice" =~ ^[0-9]+$ ]]; then
        echo "Invalid input. Please enter a number."
        continue
    fi

    if [ "$choice" -eq 0 ]; then
        echo "Exiting."
        exit 0
    fi

    if [ "$choice" -lt 1 ] || [ "$choice" -gt ${#subdirs[@]} ]; then
        echo "Invalid selection."
        continue
    fi

    selected_dir="${subdirs[$((choice-1))]}"
    test_name=$(basename "$selected_dir")

    echo "========================================"
    echo "Running install.sh..."
    (
        cd "$RAP_ROOT" || exit
        ./install.sh
    )
    
    echo "Running test: $test_name"
    echo "Directory: $selected_dir"
    echo "Command: cargo rapx -range=print_mir"
    echo "========================================"

    (
        cd "$selected_dir" || exit
        cargo rapx -range=print_mir 
        
        echo "Generating PNGs from DOT files..."
        count=0
        while IFS= read -r f; do
            if [ -f "$f" ]; then
                dot -Tpng "$f" -o "${f%.dot}.png"
                echo "Generated ${f%.dot}.png"
                ((count++))
            fi
        done < <(find . -type f -name "*.dot")

        if [ $count -eq 0 ]; then
            echo "No .dot files found."
        fi
    )
    
    echo "----------------------------------------"
    # read -p "Press Enter to continue..."
done
