#!/bin/bash

#
# Cleanup the generated Yices.epub (in build/epub)
#
# Usage: cleanup-ebup.sh build-directory
#
# Remove 'role="..." >' from all html files
# Copy the com.apple... file in META-INF
# Rebuild Yices.epub
#

if [[ $# != 1 ]]; then
  echo "Usage: $0 <build-directory>"
  exit 1
else
  buildir=$1
fi

epubfile=Yices.epub
apple=com.apple.ibooks.display-options.xml

[[ -d $buildir ]] || { echo "Directory $buildir does not exit" ; exit 1 ; } 
[[ -w $buildir/$epubfile ]] || { echo "File $buildir/$epubfile not found" ; exit 1 ; }
[[ -r $apple ]] || { echo "File $apple not found" ; exit 1 ; }

echo "Adding apple xml file"
cp $apple $buildir/META-INF/ || { echo "Error: can't copy to $buildir/META-INF" ; exit 1 ; }

cd $buildir 2> /dev/null || { echo "Failed to cd to $buildir" ; exit 1 ; }

echo "Cleaning up the html files"
for x in *.xhtml ; do
    sed -e 's/role=".*"//g' $x > $x.tmp
    mv $x.tmp $x
done

zip -q $epubfile ./META-INF/$apple
zip -q -f $epubfile
