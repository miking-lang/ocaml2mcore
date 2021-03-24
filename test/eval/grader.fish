#!/usr/bin/env fish

set exec_student $argv

set num_tests 0

set max_num_details 3
set failures

function test_one -a without_extension
    set -l extra_args $argv[2..-1]

    set -l tmpout (mktemp)
    set -l tmperr (mktemp)
    set -l tmptest (mktemp)
    command $exec_student $extra_args $without_extension".in" 1>$tmpout 2>$tmperr
    set -l code $status

    echo >> $tmpout
    echo >> $tmperr

    set -l tested_something 0
    set -l expected_out_path $without_extension".out"
    set -l expected_err_path $without_extension".err"
    set -l expected_code_path $without_extension".code"

    set -l is_failure 0

    set -l out_judgement ""
    set -l err_judgement ""
    set -l code_judgement ""

    if test -f $expected_out_path
        cat $expected_out_path > $tmptest
        echo >> $tmptest
        set tested_something 1
        set out_judgement "(✓) "
        echo Diff with $expected_out_path 1>&2 "(< expected, > got)"
        diff -wB (tr '\n' ' ' < $tmptest | psub) (tr '\n' ' ' < $tmpout | psub) 1>&2
        if test $status -ne 0
            set is_failure 1
            set out_judgement "(✗) "
        end
    else
        echo "Not checking stdout, this is what was printed:" 1>&2
        cat $tmpout 1>&2
    end
    if test -f $expected_err_path
        cat $expected_err_path > $tmptest
        echo >> $tmptest
        set tested_something 1
        set err_judgement "(✓) "
        echo Diff with $expected_err_path 1>&2 "(< expected, > got)"
        diff -wB (tr '\n' ' ' < $tmptest | psub) (tr '\n' ' ' < $tmperr | psub) 1>&2
        if test $status -ne 0
            set is_failure 1
            set err_judgement "(✗) "
        end
    else
        echo "Not checking stderr, this is what was printed:" 1>&2
        cat $tmperr 1>&2
    end
    if test -f $expected_code_path
        set tested_something 1
        set code_judgement "(✓) "
        echo Diff with $expected_code_path 1>&2
        if test $code -ne (cat $expected_code_path)
            echo "Different return code, got $code, expected "(string trim (cat $expected_code_path)) 1>&2
            set is_failure 1
            set code_judgement "(✗) "
        end
    else
        echo "Not checking exitcode, got $code" 1>&2
    end

    if test $is_failure -eq 1 -a (count $failures) -lt $max_num_details
        set -l number (math 1 + (count $failures))
        set -l anchor "detail-summary-$number"

        set -l details
        set --append details "<details id=\"$anchor\">"
        set --append details "<summary>"(math 1 + (count $failures))"</summary>" ""
        set --append details "## Input"
        if test (count $extra_args) -gt 0
            set --append details "Flags: "(string join " " "`"$extra_args"`")
        end
        set --append details "```"
        set --append details (cat $without_extension".in")
        set --append details "```"

        set --append details "## Expected"

        if test -f $expected_code_path
            set --append details "Return code: "(string trim (cat $expected_code_path))
        else
            set --append details "The return code is ignored in this test."
        end
        if test -f $expected_out_path
            set --append details "Stdout (we ignore whitespace when comparing):"
            set --append details "```"
            set --append details (cat $expected_out_path)
            set --append details "```"
        else
            set --append details "Stdout is ignored in this test."
        end
        if test -f $expected_err_path
            set --append details "Stderr (we ignore whitespace when comparing):"
            set --append details "```"
            set --append details (cat $expected_err_path)
            set --append details "```"
        else
            set --append details "Stderr is ignored in this test."
        end

        set --append details "## Actual"

        set --append details $code_judgement"Your return code: "$code

        set --append details $out_judgement"Your stdout:"
        set --append details "```"
        set --append details (cat $tmpout)
        set --append details "```"

        set --append details $err_judgement"Your stderr:"
        set --append details "```"
        set --append details (cat $tmperr)
        set --append details "```"

        set --append details "The command that was run was:"
        set --append details "```"
        set --append details "$exec_student $extra_args $without_extension.in"
        set --append details "```"

        set --append details "</details>"

        set --append failures (string join \n -- $details | string collect)

        echo "[<a href=\"#$anchor\">$number</a>]"
    end

    rm $tmpout $tmperr $tmptest

    if test $tested_something -eq 0
        echo "WARNING: none of \"$expected_out_path\", \"$expected_err_path\", and \"$expected_code_path\" exist, this test holds vacuously." 1>&2
    end

    return $is_failure
end

function do_test -a turnstile bar dir
    echo 1>&2
    echo Testing $dir 1>&2
    set -l result 0
    set -l tested_something 0
    set -l extra_args $argv[4..-1]

    set -l current_test_fails 0
    set -l fail_count 0
    set -l total_count 0

    echo "Flags:" $extra_args 1>&2

    set -l detail_links

    for test_case in $dir/*.in
        set tested_something 1
        set num_tests (math $num_tests + 1)

        set --append detail_links (test_one (string split -r -m1 . $test_case)[1] $extra_args)

        set fail_count (math $fail_count + $status)
        set total_count (math $total_count + 1)

    end

    if test $tested_something -eq 0
        echo "WARNING: no *.in files in \"$dir\", test holds vacuously." 1>&2
    end

    if test $fail_count -eq 0
        echo $turnstile"(✓) "(basename $dir)": OK ($total_count)"
    else
        echo $turnstile"(✗) "(basename $dir)" ("$fail_count" out of "$total_count" tests failed)"
        cat $dir/info | fmt -w 60 -s | sed -e 's/^/'$bar'    /'
        if test (count $detail_links) -gt 0
            echo "Additional details:" (string join ", " $detail_links) | sed -e 's/^/'$bar'    /'
        end
    end
end

function discover_tests -a turnstile bar dir
    set -l extra_args_top $argv[4..-1]
    for next_dir in $dir/*/
        set -l extra_args $extra_args_top
        if test -f $next_dir/extra_flags
            set extra_args $extra_args (cat $next_dir/extra_flags)
        end
        if test -f $next_dir/info
            do_test $turnstile $bar $next_dir $extra_args
        else
            echo $turnstile(basename $next_dir)
            discover_tests "├─ " "│  " $next_dir $extra_args | sed -e 's/^/'$bar'/'
        end
    end
end

set -l extra_args
if test -f extra_flags
    set extra_args $extra_args (cat extra_flags)
end

if test -f note
    cat note
end

echo "<pre>"
discover_tests "" "" . $extra_args
echo "</pre>"

string collect -- $failures

echo 1>&2
echo "Ran $num_tests tests in total." 1>&2
