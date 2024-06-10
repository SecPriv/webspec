#!/usr/bin/env wish

package require Tk
package require Thread
package require ctext
package require ttk::theme::arc

set webspecdir [file join [file dirname [ file normalize [ info script ]]] {../}]
set idlestatus {✅ Ready}

wm title . {WebSpec GUI}
bind . <Control-q> exit
wm protocol . WM_DELETE_WINDOW exit
option add *tearOff 0

ttk::style theme use arc

grid [ttk::frame .f0] -sticky nsew -row 0 -column 0
grid [ttk::label .f0.l0] -sticky nsew -row 0 -column 1
grid [ttk::button .f0.b1 -text {⏹️ Stop} -state disabled] -sticky nsew -row 0 -column 2 -padx 6 -pady 6
grid [ttk::button .f0.b0 -text {▶️ Run}] -sticky nsew -row 0 -column 4 -padx 6 -pady 6
grid [ttk::button .f0.b2 -text "⚙️ Verify" -state disabled] -sticky nsew -row 0 -column 3 -padx 6 -pady 6
grid [ttk::button .f0.b3 -text "🗎 Browser Model" -state normal] -sticky nsew -row 0 -column 0 -padx 6 -pady 6
grid [ttk::panedwindow .p0 -orient horizontal] -sticky nsew -row 1 -column 0
.p0 add [ttk::frame .p0.f1]
grid [ttk::treeview .p0.f1.v0 -xscrollcommand {.p0.f1.s3 set} -yscrollcommand {.p0.f1.s0 set}] -sticky nsew -row 0 -column 0
grid [ttk::scrollbar .p0.f1.s0 -orient vertical -command {.p0.f1.v0 yview}] -sticky ns -row 0 -column 1
grid [ttk::scrollbar .p0.f1.s3 -orient horizontal -command {.p0.f1.v0 xview}] -sticky ew -row 1 -column 0
.p0 add [ttk::frame .p0.f2]
grid [ctext .p0.f2.t0 -width 80 -yscrollcommand {.p0.f2.s1 set}] -sticky nsew -row 0 -column 0
grid [ttk::scrollbar .p0.f2.s1 -orient vertical -command {.p0.f2.t0 yview}] -sticky ns -row 0 -column 1
.p0 add [ttk::frame .p0.f3]
grid [ctext .p0.f3.t1 -width 80 -state disabled -wrap none -yscrollcommand {.p0.f3.s2 set} -xscrollcommand {.p0.f3.s3 set} -linemap 0] -sticky nsew -padx 0 -pady 0 -row 0 -column 0
grid [ttk::scrollbar .p0.f3.s2 -orient vertical -command {.p0.f3.t1 yview}] -sticky ns -row 0 -column 1
grid [ttk::scrollbar .p0.f3.s3 -orient horizontal -command {.p0.f3.t1 xview}] -sticky ew -row 1 -column 0
grid [ttk::frame .f4 -relief flat -borderwidth 4] -sticky nsew -row 2 -column 0
grid [ttk::label .f4.l2 -text $idlestatus] -sticky nsew -row 0 -column 0
grid [ttk::progressbar .f4.o0] -sticky nsew -row 0 -column 1
grid rowconfigure .f4 0 -weight 1
grid rowconfigure .p0.f3 0 -weight 1
grid rowconfigure .p0 0 -weight 1
grid rowconfigure .p0.f2 0 -weight 1
grid rowconfigure .p0.f1 0 -weight 1
grid rowconfigure . 1 -weight 1
grid rowconfigure .f0 0 -weight 1
grid columnconfigure .f4 0 -minsize 250
grid columnconfigure .f4 1 -weight 1
grid columnconfigure .p0.f3 0 -weight 1
grid columnconfigure .p0.f2 0 -weight 1
grid columnconfigure .p0 0 -weight 1
grid columnconfigure .p0 1 -weight 1
grid columnconfigure .p0 2 -weight 2
grid columnconfigure .p0.f1 0 -weight 1
grid columnconfigure . 0 -weight 1
grid columnconfigure .f0 1 -weight 1


proc configure_code_browser {code} {
    $code configure -linemap_markable 0 -relief sunken  -padx 8 -pady 8 -relief flat -highlightcolor LightGray -highlightbackground LightGray -highlightthickness 1
    $code.l configure -relief flat -bg #efefef -fg gray
    ctext::addHighlightClass $code vkeywords DarkOrange [list Definition Inductive Variant Record From Require Import Load Definition Inductive Theorem Proof Qed InlineRelation With Depth Set Extract Query Using Lemma Array Size]
    ctext::addHighlightClass $code mlkeywords DarkSalmon [list forall exists let in as Prop True False true false try]
    ctext::addHighlightClass $code tactics DarkBlue [list intros unfold destruct specialize congruence auto tauto remember induction destruct case_eq simpl subst apply assert eapply split firstorder rewrite]
    ctext::addHighlightClassForRegexp $code comments green {\(\*(.|\n)*?\*\)}
    ctext::addHighlightClassForRegexp $code numbers green {[^a-zA-Z][0-9]+}
}

set code .p0.f2.t0
$code configure -width 100 -state disabled
configure_code_browser $code

set output .p0.f3.t1
$output configure -state disabled -relief sunken -padx 8 -pady 8 -relief flat -highlightcolor LightGray -highlightbackground LightGray -highlightthickness 1 -highlight 1
ctext::addHighlightClassForRegexp $output level red {level: [0-9]+}
ctext::addHighlightClassForRegexp $output log blue {^.*\. \. \.$}
ctext::addHighlightClassForRegexp $output log blue {^.*(Output|Trace):.*$}
ctext::addHighlightClassForRegexp $output build DarkOrange {Build_[^ ]+}


set status .f4.l2
set progress .f4.o0
set run .f0.b0
set stop .f0.b1
set verify .f0.b2

proc clear_output {} {
    global output
    $output configure -state normal
    $output delete 1.0 end
    $output configure -state disabled
}

proc insert_output {data} {
    global output
    $output configure -state normal
    set last [$output index end]
    $output fastinsert end $data
    $output highlight [expr $last - 1.0] end
    $output configure -state disabled
    $output see end
}

proc stop_callback {} {
    global progress status run idlestatus stop
    $progress stop
    $progress configure -mode determinate
    $status configure -text $idlestatus
    $run configure -state normal
    $stop configure -state disabled
}

$stop configure -command {
    exec docker kill webspec
    stop_callback
}

$run configure -command {
    $progress configure -mode indeterminate
    $progress start
    $status configure -text "💻 Running [$treeview selection]..."
    $run configure -state disabled
    $stop configure -state normal
    clear_output

    set runtid [thread::create]
    thread::send -async $runtid {
        proc worker {parentid webspecdir filename} {
            set io [open "|stdbuf -o0 $webspecdir/webspec run [exec basename $filename {.v}] 2>@1" r]
            fconfigure $io -buffering line
            while {![eof $io]} {
                set line [gets $io]
                if {$line ne ""} {
                    thread::send $parentid [list insert_output "$line\n"]
                }
            }
            catch {close $io}
            thread::send $parentid {stop_callback}
        }
    }
    thread::send -async $runtid [list worker [thread::id] $webspecdir [$treeview selection]]
}

set treeview .p0.f1.v0
$treeview configure -columns "trace" -selectmode browse
$treeview column "#0" -anchor w -stretch 1 -minwidth 200
$treeview heading "#0" -text "Invariant"
$treeview column "trace" -width 60 -anchor center -stretch 0
$treeview heading "trace" -text "Trace"
set modeldir "$webspecdir/model"
set tracedir "$webspecdir/traces"
foreach fname [lsort [glob "$modeldir/*Invariant.v"]] {
    set basename [exec basename "$fname"]
    set invname [exec basename "$basename" {.v}]
    $treeview insert {} end -id $basename -text $basename
    if {[file exists "$tracedir/$invname.trace.z3"]} {
        $treeview set $basename trace "✔"
    }
}

bind $treeview <<TreeviewSelect>> {
    $code configure -state normal
    $code replace 1.0 end [exec cat [join [list $modeldir [$treeview selection]] "/"]]
    $code highlight 1.0 end
    $code configure -state disabled
    $verify configure -state disabled
    if {[$treeview set [$treeview selection] trace] ne {} } {
        $verify configure -state normal
    }
}
$treeview selection set [lindex [$treeview children {}] 0]

set model .f0.b3
$model configure -command {
    catch {
        toplevel .mb
        wm title .mb {WebSpec Browser Model}

        grid [ttk::notebook .mb.n0] -row 0 -column 0 -sticky nsew
        .mb.n0 add [ttk::frame .mb.n0.f0] -text "Overview"
        grid [tk::text .mb.n0.f0.t0 -yscrollcommand {.mb.n0.f0.s0 set} -xscrollcommand {.mb.n0.f0.s1 set}] -row 0 -column 0 -sticky nsew
        grid [ttk::scrollbar .mb.n0.f0.s0 -orient vertical -command {.mb.n0.f0.t0 yview}] -sticky ns -row 0 -column 1
        grid [ttk::scrollbar .mb.n0.f0.s1 -orient horizontal -command {.mb.n0.f0.t0 xview}] -sticky ew -row 1 -column 0
        .mb.n0 add [ttk::frame .mb.n0.f1] -text "Source Code"
        grid [ctext .mb.n0.f1.t1 -yscrollcommand {.mb.n0.f1.s1 set}] -row 0 -column 0 -sticky nsew
        grid [ttk::scrollbar .mb.n0.f1.s1 -orient vertical -command {.mb.n0.f1.t1 yview}] -sticky ns -row 0 -column 1
        grid rowconfigure .mb.n0.f0 0 -weight 1
        grid rowconfigure .mb 0 -weight 1
        grid rowconfigure .mb.n0 0 -weight 1
        grid rowconfigure .mb.n0.f1 0 -weight 1
        grid columnconfigure .mb.n0.f0 0 -weight 1
        grid columnconfigure .mb 0 -weight 1
        grid columnconfigure .mb.n0 0 -weight 1
        grid columnconfigure .mb.n0.f1 0 -weight 1

        set moverview .mb.n0.f0.t0
        $moverview configure -state disabled -relief sunken -padx 0 -pady 0 -relief flat -highlightcolor LightGray -highlightbackground LightGray -highlightthickness 1
        image create photo model -file "$webspecdir/gui/img/model.png"
        image create photo resizedmodel
        resizedmodel copy model -subsample 2 2
        $moverview image create 1.0 -image resizedmodel

        set mcode .mb.n0.f1.t1
        configure_code_browser $mcode
        $mcode configure -state normal
        $mcode replace 1.0 end [exec cat [join [list $modeldir "Browser.v"] "/"]]
        $mcode highlight 1.0 end
        $mcode configure -state disabled
    }
}
