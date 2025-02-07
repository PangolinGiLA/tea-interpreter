#!/bin/bash
TMP_OUT=""
TMP_ERR=""
OK_CNT=0
ER_CNT=0

mk_temps() {
    TMP_OUT=$(mktemp)
    TMP_ERR=$(mktemp)
}
rm_temps() {
    rm $TMP_OUT
    rm $TMP_ERR
}

run_test() {
    ./interpreter $1
}

test_file() {
    file=$1
    echo "Running test $file..."
    run_test $file > $TMP_OUT 2> $TMP_ERR

	if diff ${file%tea}out $TMP_OUT>/dev/null
	then
        echo -e "OK"
        ((OK_CNT++))
    else
        echo -e "ERROR IN OUTPUT"
        ((ER_CNT++))
    fi

	if diff ${file%tea}err $TMP_ERR>/dev/null
    then
        echo -e "OK"
        ((OK_CNT++))
    else
        echo -e "ERROR IN ERROR"
        ((ER_CNT++))
    fi

	echo ""
}

if [ $# -eq 0 ]; then
    mk_temps
    echo "Running all tests..."
    for mod in bad good; do
        for file in ./$mod/*.tea; do
            test_file $file
        done
    done
    rm_temps

    echo "Tests passed: $OK_CNT"
    echo "Test failed: $ER_CNT"
    if [ $ER_CNT -eq 0 ]; then
        exit 0
    else
        exit 1
    fi
fi

wait_to_clear() {
    read -p "Press enter to continue..."
    clear
}

interactive_in_mod() {
    mod=$1
    start=$2
    started=0
    echo "Running tests in $mod..."
    wait_to_clear

    for file in ./$mod/*.tea; do
        f=$(basename "$file" .tea)
        if [[ $f == $start* ]]; then # wildcard match
            started=1
        fi
        if [ $started -eq 1 ]; then
            printf "Test $file:\n"
            cat $file
            printf "\nOutput:\n"
            run_test $file
            printf "\n"
            wait_to_clear
        fi
    done
}

if [ "$1" == "--interactive" ]; then
    echo "Running interactive tests..."
    wait_to_clear

    if [ $# -gt 1 ]; then
        mod=$2
        start=$3
        interactive_in_mod $mod $start
    else
        for mod in bad good; do
            interactive_in_mod $mod
        done
    fi
    exit 0
fi

dir=$1
test=$2
echo "Running $dir test $test..."
run_test "./$dir/$test.tea"