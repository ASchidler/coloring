cmake -DCMAKE_BUILD_TYPE=Release .
make
mkdir benchmark-results
./planarity-cpp -s2 instances/reecn34307.instance.txt
