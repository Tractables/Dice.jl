TO=/space2/tjoa/tuning-output
cat "$(dirname $(find $TO -name *BSmallTrainedGenerator*))/log.log" | head -n 1
cat "$(dirname $(find $TO -name *RLSDThinSmallGenerator*))/log.log" | head -n 1
cat "$(dirname $(find $TO -name *SLSDThinEqWellLR30Bound10Generator*))/log.log" | head -n 1
cat "$(dirname $(find $TO -name *SBespokeACELR03Bound10Generator*))/log.log" | head -n 1

