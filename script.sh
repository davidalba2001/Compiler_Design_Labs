
#!/bin/bash

current_path=$(pwd)

folder_name="${current_path}/labs_notebooks.tar"

archivos=$(ls ${folder_name}/*.tar.gz)
for archivo in $archivos
do
    tar -xf "$archivo" -C "$current_path"
done
