#! /usr/bin/env bash

# Dune does not support odoc 3.0.
# This script handles the documentation generation pipeline from scratch.

VERBOSE=false
if [[ "$1" == "-v" ]]; then
    VERBOSE=true
fi

log() {
    if $VERBOSE; then
        echo "$@"
    fi
}

DOC_DIR="doc"
BUILD_DIR="_build/_doc"
PKG_ID="viper"
BUILD_PATH=$BUILD_DIR/$PKG_ID

rm -rf $BUILD_DIR
mkdir $BUILD_DIR

# Compiling
for f in $DOC_DIR/*.mld
do
    log "Compiling $f"
    odoc compile \
        $f \
        --enable-missing-root-warning \
        --output-dir $BUILD_DIR \
        --parent-id $PKG_ID \
        -I $BUILD_PATH
done

# Linking
for f in $BUILD_PATH/*.odoc
do
    log "Linking $f"
    odoc link \
        $f \
        --enable-missing-root-warning \
        -P viper:$BUILD_PATH \
        --current-package viper \
        -I $BUILD_PATH
done

# Indexing
rm -f $BUILD_PATH/linked_files.txt
for f in $BUILD_PATH/*.odocl; do echo "$f"; done > $BUILD_PATH/linked_files.txt

log "Indexing..."
odoc compile-index \
    --enable-missing-root-warning \
    -o $BUILD_PATH/indexed.odoc-index \
    --root "viper:$BUILD_PATH" \
    --warn-error \
    --file-list $BUILD_PATH/linked_files.txt
    # $BUILD_PATH/*.odocl
    

log "Building sidebar"
odoc sidebar-generate \
    $BUILD_PATH/indexed.odoc-index \
    --enable-missing-root-warning \
    -o $BUILD_PATH/sidebar.odoc-sidebar

# Generating HTML files
for f in $BUILD_PATH/*.odocl
do
    log "Generating $f"
    odoc html-generate \
        $f \
        --enable-missing-root-warning \
        --output-dir $BUILD_PATH/_html/ \
        --sidebar $BUILD_PATH/sidebar.odoc-sidebar
        # DO NOT use the semantic-uris flag. I don't know why but it breaks everything.
done

# Generating Support Files
odoc support-files \
    -o $BUILD_PATH/_html/