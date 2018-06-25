#!/usr/bin/sed -E

# Translate older Vernacular commands of the plugin to their newer versions.

s/^Find ornament ([A-Za-z0-9_']+) ([A-Za-z0-9_']+) as ([A-Za-z0-9_']+)/Ornament \3 from \1 to \2/;
s/^Apply ornament ([A-Za-z0-9_']+) ([A-Za-z0-9_']+) in ([A-Za-z0-9_']+) as ([A-Za-z0-9_']+)/Ornamental Application \4 from \3 using \1 \2/;
s/^Reduce ornament ([A-Za-z0-9_']+) ([A-Za-z0-9_']+) in ([A-Za-z0-9_']+) as ([A-Za-z0-9_']+)/Ornamental Reduction \4 from \3 using \1 \2/;
s/^Higher lift ([A-Za-z0-9_']+) ([A-Za-z0-9_']+) in ([A-Za-z0-9_']+) as ([A-Za-z0-9_']+)/Ornamental Modularization \4 from \3 using \1 \2/;
