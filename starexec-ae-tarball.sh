make clean
make bin
rm  -rf bin bin.tar.gz
mkdir bin
cp _build/install/default/bin/alt-ergo bin/run

#echo "./run -sat-solver Tableaux \$1" >> bin/starexec_run_tab
echo "./run -sat-solver CDCL-Tableaux     \$1" >> bin/starexec_run_cdcl-tab

chmod 755 bin/*
tar cvfz bin.tar.gz bin


#make clean
#make run
#rm  -rf bin bin.tar.gz
#mkdir bin
#cp run bin/run
#echo "./run -silent -minimal-bj \$1" >> bin/starexec_run_default
#chmod 755 bin/starexec_run_default
#tar cvfz bin.tar.gz bin
