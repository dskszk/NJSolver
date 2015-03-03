
echo $1 | ./NJSolver > ${2%.pdf}.tex
lualatex ${2%.pdf}.tex > /dev/null

