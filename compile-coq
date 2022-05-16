# Arg 1 - takes the file to be compiled (full path). If not supplied, the .ds file to be compiled should be in the current directory (and the only .ds file in the directory).
# Note, coqc must be on the path (if using opam, eval $(opam env) may need to be run, or possibly added to this script along with a relevant opam switch ...)

set -e

CONTRACT_NAME=$1 # Don't include the ".ds"

rm -rf "$CONTRACT_NAME" # You may want to remove this line if you do not wish the folder to be deleted on every run e.g. if filling in some proofs within the auto-generated files.
dsc "$CONTRACT_NAME.ds" coq
cd "$CONTRACT_NAME"

coqdep -f _CoqProject > .coqdeps.d
coq_makefile -arg "-quiet" -f _CoqProject -o core.make 
make -f core.make

cd ..