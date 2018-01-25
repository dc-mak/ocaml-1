#!/usr/bin/env zsh

set -eo pipefail

# Install compiler as opam switch
# https://github.com/ocaml/opam/issues/2531#issuecomment-235377458

n=10

tmp=tmp.txt
sizes_csv="sizes_$1.csv"
time_means_csv="time_means_$1.csv"
time_varis_csv="time_varis_$1.csv"

size_col=size_col.txt
time_mean_col=time_mean_col.txt
time_vari_col=time_vari_col.txt

function measure {
    
    local filename=$1

    # Compile
    echo "   compiling $filename"
    ../ocamlopt -noassert -unsafe -unsafe-string -fPIC -nodynlink -inline 100 "$filename" -o "$filename.exe"
    local time_mean=0.0
    local t=0.0
    local -a buffer

    # Execution time
    echo "   running $filename.exe"
    for ((i = 0; i < n; i++))
    do
        t=$({ time ./"$filename.exe" 7 > run_log.txt; } 2> "$tmp"; cat "$tmp" | sed -r 's/.*([0-9]+\.[0-9]+) total/\1/g')
        (( time_mean = time_mean + t ))
        buffer+=($t)
    done

    # Size
    local size=$(wc -c < "$filename.exe")
    echo "   size of $filename.exe is $size"
    echo "$size" >> "$size_col"

    # Mean
    (( time_mean = time_mean / n ))
    echo "   runtime of $filename.exe is $time_mean"
    echo "$time_mean" >> "$time_mean_col"

    # Standard deviation
    local time_vari=$(echo "$buffer" | awk -vM="$time_mean" '{for(i=1;i<=NF;i++){sum+=($i-M)*($i-M)};print (sum/NF)}')
    echo "   vari of $buffer for $filename.exe is $time_vari"
    echo "$time_vari" >> "$time_vari_col"

}

# Micro-benchmarks
to_measure=( 
    binarytrees.ml
    fasta.ml
    mandelbrot.ml
    # fannkuchredux.ml # requires Unix.cma
    # safepoints.ml # loops forever
    nbody.ml
    ray.ml
    tight.ml
)

function measure_all {

    echo "   resetting col files"
    local l_max=$1

    printf "%03d\n" "$l_max" > "$size_col"
    printf "%03d\n" "$l_max" > "$time_mean_col"
    printf "%03d\n" "$l_max" > "$time_vari_col"

    for file in $to_measure
    do
        measure "$file"
    done

    echo "   pasting columns"

    paste -d, "$sizes_csv" "$size_col" > "$tmp"; mv "$tmp" "$sizes_csv"
    truncate -s 0 "$size_col"

    paste -d, "$time_means_csv" "$time_mean_col" > "$tmp"; mv "$tmp" "$time_means_csv"
    truncate -s 0 "$time_mean_col"

    paste -d, "$time_varis_csv" "$time_vari_col" > "$tmp"; mv "$tmp" "$time_varis_csv"
    truncate -s 0 "$time_vari_col"
}

# Get correct compiler

git checkout 4.06
# git checkout trunk

# Set up column header
echo "resetting csv files"
echo "prog/lmax" > "$sizes_csv"
echo "prog/lmax" > "$time_means_csv"
echo "prog/lmax" > "$time_varis_csv"
# Set up row names
for file in $to_measure
do
    echo "listing $file in csv files"
    echo "$file" >> "$sizes_csv"
    echo "$file" >> "$time_means_csv"
    echo "$file" >> "$time_varis_csv"
done
# Iterate for each L_max
for ((j = 2; j < 30; j++))
do
    let "k = j * 6"
    echo "k=$k"
    sed -i -- "s/let l_max = [0-9]*/let l_max = $k/g" ../asmcomp/asmgen.ml
    make -C .. ocamlopt > /dev/null
    echo "   measuring"
    measure_all "$k"
done

git reset --hard
git checkout b5ac7b1d94c6e5c7fb5e66ac118e21846de8e115
# git checkout 64fb4f58aceec9033038f3d8398e000391fdf433

echo "no lmax"
make -C .. ocamlopt > /dev/null
echo "   measuring"
measure_all 0
