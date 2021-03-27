#!/usr/bin/env fish

set -l miking_dir "../../../../miking-lang/miking"

set exec_student $argv

set -l tmpdir (mktemp -d)

set -l comp_out $tmpdir"/comp.out"
set -l comp_err $tmpdir"/comp.err"

set -l prog "./comp"

set -l prog_out $tmpdir"/prog.out"
set -l prog_err $tmpdir"/prog.err"

set -l has_failed 0

command $exec_student 1>$comp_out 2>$comp_err
set -l code $status

if test $code -ne 0
    set has_failed 1
end

echo "### MCore program" 1>&2
echo "Exitcode: "$code 1>&2
echo "Stdout:" 1>&2
echo "```" 1>&2
cat $comp_out 1>&2
echo "```" 1>&2
echo "Stderr:" 1>&2
echo "```" 1>&2
cat $comp_err 1>&2
echo "```" 1>&2

if test $has_failed -ne 1
    echo "### OCaml program" 1>&2
    echo "Command: `mi $miking_dir/src/main/mi.mc -- compile $comp_out`" 1>&2
    command         mi $miking_dir/src/main/mi.mc -- compile $comp_out
    set code $status

    echo "Program:" 1>&2
    echo "```" 1>&2
    $prog 1>$prog_out 2>$prog_err
    echo "```" 1>&2

    echo "Stderr (ignored):" 1>&2
    echo "```" 1>&2
    cat $prog_err 1>&2
    echo "```" 1>&2

    echo "Stdout:" 1>&2
    echo "```" 1>&2
    cat $prog_out 1>&2
    echo "```" 1>&2

    # NOTE(vipa, 2020-11-24): This should go to stdout, that's intentional
    cat $prog_out

end

if test $has_failed -eq 1
    echo "fail" 1>&2
else
    echo "success" 1>&2
end

rm -rf $tmpdir

exit $code
