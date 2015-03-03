
echo $1 | ./NJSolver > ${2%.pdf}.tex
latex ${2%.pdf}.tex > /dev/null

