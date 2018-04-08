if [ "$#" -ne 3 ]; then
    echo "Illegal number of parameters. Run script with:"
    echo "$0 arg1 arg2 arg3"
    echo "where"
    echo "arg1: path to virtualenvironment of python2 with z3 installed"
    echo "arg2: path to python solution file .py"
    echo "arg3 :path to folder with tests"
    exit 1
fi

VENV=`realpath ${1%/}`
solution=`realpath $2`
test_folder=`realpath ${3%/}`

CORRECT_OUT_EXT='.out'
IN_EXT='.in'
OUT_EXT='.output'

source $VENV/bin/activate

for file in $test_folder/*$IN_EXT
do
    filename=`basename $file $IN_EXT`
    python $solution < $test_folder/$filename$IN_EXT > $test_folder/$filename$OUT_EXT
    diff $test_folder/${filename}$OUT_EXT $test_folder/${filename}$CORRECT_OUT_EXT >> /dev/null
    
    if [ $? -ne 0 ]; then
        echo "TEST $filename: FAILED"
    else
        echo "TEST $filename: OK"
    fi

done
