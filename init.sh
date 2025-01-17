curl -L $1 -o HW12345.html
repo=`grep -o 'cs4410/[^"]*' HW12345.html`
dirname="${repo:7}"
repolink="git@github.khoury.northeastern.edu:${repo}.git"
    
rm HW12345.html
git clone ${repolink}

files=`ls ${dirname}/*.ml`

script="if dune build; then
    make clean
    make test
    ./test
    make clean

    if [ \$# -gt 0 ]; then
        zip submission.zip Makefile ${files}
        echo 'Saved submission.zip'
    fi
else
    echo 'Build failure. Aborting...'
fi"
echo "${script}" > $dirname/run
chmod 777  $dirname/run

rm -rf "${dirname}/.git"
