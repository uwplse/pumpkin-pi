while read str; do
    grep --color=always -R --ignore-case "$str" *
done < deanonymizing-words.txt
