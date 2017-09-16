#!/usr/bin/sh
# Script to populate the Agda library file (~/.agda/libraries)

# base path
BASE_PATH=$(pwd)

# Libraries we want to add
AUTO_IN_AGDA=AutoInAgda/auto-in-agda.agda-lib
AGDA_STEROIDS=agda-steroids/agda-steroids.agda-lib

FILES=($AUTO_IN_AGDA $AGDA_STEROIDS)

# Append the files to the libraries file
for f in ${FILES[@]}; do
  echo $BASE_PATH/${f} >> ~/.agda/libraries
done

exit 0

