
echo $1 | ./NJSolver > ${2%.pdf}.tex
pdflatex ${2%.pdf}.tex > /dev/null

