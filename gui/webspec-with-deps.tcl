#! /bin/sh
# \
exec wish${TCL} "$0" ${1+"$@"}
#-------------------------------------------------------------------
# Thatch
#-------------------------------------------------------------------
namespace eval ::thatch {
	if {[package provide thatch] ne {}} { return }

	proc thatchBootstrap {{fn ""}} {
		if {$fn eq ""} { set fn [info script] }
		if {[catch {
			set f [open $fn r]
			fconfigure $f -eofchar \x1a
			read $f
			seek $f 1 current
			set d [read $f]
			close $f
		} err]} {
			return 0
		}
		if {[string length $d] == 0} { return 0 }
		uplevel #0 $d
		package require thatch
	}
	package ifneeded thatch 0.5 [namespace current]::thatchBootstrap
}

package require thatch
::thatch::thatchSetup [info script] 

source ./webspec.tcl
#-------------------------------------------------------------------

# THATCH /packages/thatch/thatch.tcl 
#
# Thatch - Tcl Attach
#
#
# Stuart Cassoff
#
# May 2009
# December 2009
# January 2010
# October 2010
# March 2012
# Summer 2012
# Spring 2018
# Version 0.1
#
# Spring 2018
# Version 0.2
#
# Summer 2018
# Version 0.3
#
# Summer 2022
# Version 0.4
#
# Summer 2022
# Version 0.5
#


[namespace eval ::thatch {

proc pkgconfig {subcommand args} {
	if {$subcommand ni [list get list]} {
		return -code error "unknown subcommand \"$subcommand\": must be get, or list"
	}
	set pkgconfig [dict create {*}{
		name	thatch
		title	Thatch
		descr	"App Builder"
		author	{Stuart Cassoff}
		when	{Summer 2022}
		version	0.5
	}]
	dict set pkgconfig importfrom [namespace current]
	dict set pkgconfig license,type ISC
	dict set pkgconfig license,text [regsub -all {^\s+|\s+$|\t} {
		Copyright (c) 2009,2018,2022 Stuart Cassoff <stwo@users.sourceforge.net>

		Permission to use, copy, modify, and distribute this software for any
		purpose with or without fee is hereby granted, provided that the above
		copyright notice and this permission notice appear in all copies.

		THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
		WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
		MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
		ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
		WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
		ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
		OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
	} {}]
	return -code {*}[expr {
	    $subcommand eq "list"
		? [llength $args] == 0
		    ? [list ok [dict keys $pkgconfig]]
		    : [list error "wrong # args: should be \"[namespace current]::pkgconfig list\""]
		: $subcommand eq "get"
		    ? [llength $args] == 1
			? [dict exists $pkgconfig [set key [lindex $args 0]]]
			    ? [list ok [dict get $pkgconfig $key]]
			    : [list error "key \"$key\" not known"]
			: [list error "wrong # args: should be \"[namespace current]::pkgconfig get key\""]
		    : [list uh oh]
	}]
}; # pkgconfig


#-------------------------------------------------------------------
# Thatch preamble and bootstrap code
#-------------------------------------------------------------------


proc preamble {{wish {0}}} {
	return "#! /bin/sh\n# \\\nexec [expr {$wish ? "wi" : "tcl"}]sh\${TCL} \"\$0\" \${1+\"\$@\"}"
}


variable bootstrap [string range {
#-------------------------------------------------------------------
# Thatch
#-------------------------------------------------------------------
namespace eval ::thatch {
	if {[package provide thatch] ne {}} { return }

	proc thatchBootstrap {{fn ""}} {
		if {$fn eq ""} { set fn [info script] }
		if {[catch {
			set f [open $fn r]
			fconfigure $f -eofchar \x1a
			read $f
			seek $f 1 current
			set d [read $f]
			close $f
		} err]} {
			return 0
		}
		if {[string length $d] == 0} { return 0 }
		uplevel #0 $d
		package require thatch
	}
	package ifneeded thatch @VER@ [namespace current]::thatchBootstrap
}

package require thatch
::thatch::thatchSetup [info script] @THATCHOPTS@

source @MAIN@
#-------------------------------------------------------------------
} 1 end-1]


#-------------------------------------------------------------------
# Other
#-------------------------------------------------------------------

proc linterleave {l1 l2} {
	set l {}
	foreach e1 $l1 e2 $l2 { lappend l $e1 $e2 }
	return $l
}

proc dgwd {def dict key args} {
	if {[dict exists $dict $key {*}$args]} {
		return [dict get $dict $key {*}$args]
	}
	return $def
}

# In My Namespace
proc imn {what} {
	return [string trimright [uplevel 1 {namespace current}] :]::$what
}

proc aliasconst {name val args} {
	if {[llength $args] % 2 != 0} { error "must be %2!" }
	foreach {n v} [linsert $args 0 $name $val] {
		interp alias {} [imn $n] {} return -level 0 $v
	}
}

proc unknownOption {opt opts} {
	set msg "unknown option \"$opt\""
	if {[llength $opts] == 0} { return $msg }
	append msg ", must be: "
	append msg [lindex $opts 0]
	if {[llength $opts] == 2} {
		append msg " or [lindex $opts 1]"
	} elseif {[llength $opts] > 2} {
		append msg ", " [join [lrange $opts 1 end-1] ", "] " or " [lindex $opts end]
	}
	return $msg
}

#-------------------------------------------------------------------
# File
#-------------------------------------------------------------------

proc openItIn {fn {mode r} args} {
	if {$fn in {- stdin}} {
		set f stdin
	} else {
		if {[string index $fn 0] eq "@"} {
			set f [string range $fn 1 end]
		} else {
			set f [open $fn $mode]
		}
	}
	if {[llength $args] > 0} {
		chan configure $f {*}$args
	}
	return $f
}

proc openItOut {fn {mode w} args} {
	if {$fn in {- stdout}} {
		set f stdout
	} else {
		set f [open $fn $mode]
	}
	if {[llength $args] > 0} {
		chan configure $f {*}$args
	}
	return $f
}

proc closeIt {f} {
	if {$f in {stdin stdout}} {
		return {}
	}
	return [chan close $f]
}

proc inhaleIt {fn args} {
	return [read [set f [openItIn $fn r {*}$args]]][closeIt $f]
}

interp alias {} [imn openIt] {} [imn openItIn]

#-------------------------------------------------------------------
# Transforms
#-------------------------------------------------------------------

proc thatchWhatTransforms {{pat *}} {
	return [lsort -dictionary [lsearch -inline -all -glob [list copy base64 zip] $pat]]
}

if {[namespace ensemble exists binary] && "encode" in [dict keys [namespace ensemble configure binary -map]] && "decode" in [dict keys [namespace ensemble configure binary -map]]} {
	namespace eval ::base64 {
		proc encode {args} { binary encode base64 {*}$args }
		proc decode {args} { binary decode base64 {*}$args }
		package provide base64 2000
	}
}; # if binary encode/decode

namespace eval ::zip {
	proc encode {args} { zlib compress   {*}$args }
	proc decode {args} { zlib decompress {*}$args }
	package provide zip 2000
}

proc thatchTransform {data process args} {
	foreach alg $args {
		if {$alg eq "copy"} { continue }
		package require $alg
		set data [::${alg}::${process} $data]
	}
	return $data
}

#-------------------------------------------------------------------
# Checksums
#-------------------------------------------------------------------

proc thatchWhatChecksums {{pat *}} {
	return [lsort -dictionary [lsearch -inline -all -glob [list md5 sha256] $pat]]
}

proc thatchChecksum {data alg} {
	package require $alg
	set ns [string map [list md5 md5 sha256 sha2] $alg]
	return [::${ns}::${alg} -hex $data]
}

proc thatchMakeChecksums {data args} {
	set cksums {}
	foreach alg [lsort -nocase -dictionary $args] {
		set alg [string tolower $alg]
		lappend cksums $alg:[thatchChecksum $data $alg]
	}
	return [join $cksums ,]
}

proc thatchCheckChecksums {data args} {
	set errs {}
	foreach cksum [lsort -nocase -dictionary [split $args ,]] {
		lassign [split $cksum :] alg sum
		set alg [string tolower $alg]
		set csum [thatchChecksum $data $alg]
		if {$csum ne $sum} {
			lappend errs [list $cksum $csum]
		}
	}
	return $errs
}

#-------------------------------------------------------------------
# Thatch
#-------------------------------------------------------------------

#-------------------------------------------------------------------
#
#	i == file info
#	N == \n
#	Z == ^Z
#
#	ZN# THATCH iiiiiiiiiiiiiiiN
#	||__sig___||__file info__||
#	|          |file info line|
#	|_____file info chunk_____|
#
#
#	file info       fis
#	file info line  fil
#	file info chunk fic
#	file info dict  fid
#	file spec       fs
#
#-------------------------------------------------------------------


#
# File Spec (fs) fields
#
proc fsFields {} {
	return [list name size mtime base64 zip md5 sha256 remove rehome modbase]
}

proc fid->fis {fid} {
	set name [dict get $fid name]
	if {[dict exists $fid rehome]} {
		if {[dict get $fid rehome] ne ""} {
			set name [dict get $fid rehome]
		}
		dict unset fid name
		dict unset fid rehome
	}
	if {[dict exists $fid modbase] && [dict get $fid modbase] eq {}} {
		dict unset fid modbase
	}
	return "$name $fid"
}

proc fis->fid {fis} {
	set q [dict create name [lindex $fis 0] {*}[lrange $fis 1 end]]
}

proc fidFields {args} {
	return "name transforms checksums size stored-size mtime modbase"
}

proc newFid {args} {
	return [dict create ${*}[fidFields] {*}$args]
}

#
# File Spec (fs) -> File Info Dict (fid)
#
proc fs->fid {fs {dv {}}} {
	if {$dv ne ""} { upvar $dv data }
	lassign $fs {*}[fsFields]
	set transforms [list]
	set chanconf [dict create]

	# If zip & base64 do zip first
	if {$zip == 1} {
		lappend transforms zip
		dict set chanconf -translation binary
	}
	if {$base64 == 1} {
		lappend transforms base64
		dict set chanconf -translation binary
	}

	set fid [dict create name $name]

	if {[llength $transforms] > 0} { dict set fid transforms $transforms }

	if {$dv eq ""} {
		return $fid
	}

	set filename $name
	file stat $filename s
	set data [inhaleIt $filename {*}$chanconf]

	set algs [list]
	if {$md5 == 1}  { lappend algs md5 }
	if {$sha256 == 1} { lappend algs sha256 }

	set checksums [thatchMakeChecksums $data {*}$algs]
	set data [thatchTransform $data encode {*}$transforms]
	set s(stored-size) [string bytelength $data]

	if {$checksums ne ""} {
		dict set fid checksums $checksums
	}

	if {$size == 1} {
		dict set fid size $s(size)
		if {$s(size) != $s(stored-size)} {
			dict set fid stored-size $s(stored-size)
		}
	}

	if {$mtime == 1} {
		dict set fid mtime $s(mtime)
	}

	dict set fid rehome $rehome
	dict set fid modbase $modbase

	return $fid
}

#
# Writes a Thatch header
#
proc fid->fic {of fid} {
	puts -nonewline $of [^Z][sig][fid->fis $fid]\n
}

#
# Writes a File Info Chunk (fic): the Thatch header and the file
# from a File Spec (fs)
#
proc fs->fic {of fs} {
	set fid [fs->fid $fs data]
	fid->fic $of $fid
	puts -nonewline $of $data
}

#
# Arguments (ags) -> File Spec List (fsl)
#
proc ags->fsl {ags} {
	set fsl [list]
	#         name      var     val default
	set al [list {*}{
		{ -         doArgs    0  1 }
		{ allsize   allSize   1 -1 }
		{ allmtime  allMtime  1 -1 }
		{ allbase64 allBase64 1 -1 }
		{ allzip    allZip    1 -1 }
		{ allmd5    allMd5    1 -1 }
		{ allsha256 allSha256 1 -1 }
		{ noallsize   allSize   0 -1 }
		{ noallmtime  allMtime  0 -1 }
		{ noallbase64 allBase64 0 -1 }
		{ noallzip    allZip    0 -1 }
		{ noallmd5    allMd5    0 -1 }
		{ noallsha256 allSha256 0 -1 }
		{ size      size      1 -1 }
		{ mtime     mtime     1 -1 }
		{ base64    base64    1 -1 }
		{ zip       zip       1 -1 }
		{ md5       md5       1 -1 }
		{ sha256    sha256    1 -1 }
		{ nosize    size      0 -1 }
		{ nomtime   mtime     0 -1 }
		{ nobase64  base64    0 -1 }
		{ nozip     zip       0 -1 }
		{ nomd5     md5       0 -1 }
		{ nosha256  sha256    0 -1 }
		{ allremove allRemove 1  0 }
		{ remove    remove    1 -1 }
		{ file      argIsFs   1  0 }
		{ home      argIsHm   1  0 }
		{ rehome    argIsRHm  1  0 }
		{ modbase   argIsMb   1  0 }
		{ rename    argIsRen  1  0 }
	}]
	foreach a $al { set [lindex $a 1] [lindex $a 3] }

	set    homedir ""
	set  rehomedir ""
	set modbasedir ""
	set resetOpts 1
	set gopts {}
	# Arg options override FileSpec options
	foreach arg $ags {
		if {$resetOpts} {
			set resetOpts 0
			set rename ""
			foreach a $al {
				# Only reset specific options
				if {[lindex $a 0] ni [fsFields]} { continue }
				set [lindex $a 1] [lindex $a 3]
			}
		}
		set home    ""
		set rehome  ""
		set modbase ""
		if {$argIsHm} {
			set argIsHm 0
			set homedir $arg
			continue
		}
		if {$argIsRHm} {
			set argIsRHm 0
			set rehomedir $arg
			continue
		}
		if {$argIsMb} {
			set argIsMb 0
			set modbasedir $arg
			continue
		}
		if {$argIsRen} {
			set argIsRen 0
			set rename $arg
			continue
		}
		# Does arg look like an option or a FileSpec?
		if {$doArgs && !$argIsFs && [string index $arg 0] eq "-"} {
			# Valid options are assigned to vars and added to gopts
			if {[set i [lsearch -index 0 $al [string range $arg 1 end]]] != -1} {
				set [lindex $al $i 1] [lindex $al $i 2]
				if {[string range $arg 1 3] eq "all" || [string range $arg 1 5] eq "noall"} {
					lappend gopts [string range $arg 1 end]
				}
				continue
			}
		}
		set argIsFs 0
		# Check FileSpec for options
		set opts [lassign [split $arg %] name]
		foreach opt $opts {
			if {$argIsHm} {
				set argIsHm 0
				set home $opt
				continue
			}
			if {($opt ni $gopts || $opt eq "home") && [set i [lsearch -index 0 $al $opt]] != -1} {
				set [lindex $al $i 1] [lindex $al $i 2]
			}
		}

		# Empty name can be used to set global options
		if {$name eq ""} {
			set resetOpts 1
			continue
		}

		# Use defaults if options not supplied
		#foreach n {size mtime base64 zip md5 sha256 remove rehome modbase} {}
		foreach n {size mtime base64 zip md5 sha256 remove} {
			if {[set $n] == -1} { set $n [set all[string totitle $n]] }
		}

		if {$home eq ""} {
			set home [expr {[string index $name 0] eq "/" ? "" : $homedir}]
		}

		set file [file join $home $name]

		if {$rename ne ""} {
			set name $rename
		}
		if {$rehomedir ne ""} {
			set rehome [file join [expr {[string index $name 0] eq "/" ? "" : $rehomedir}] $name]
		}
		if {$modbasedir ne "" && [regexp -- {^([_[:alpha:]][:_[:alnum:]]*)-([[:digit:]].*)[.]tm$} [file tail $file] -> pn pv]} {
			set modbase $modbasedir
		}

		lappend fsl [list $file $size $mtime $base64 $zip $md5 $sha256 $remove $rehome $modbase]

		set resetOpts 1
	}

	return $fsl
}

proc thatchOpen {fn {dir {in}}} {
	if {$dir eq "out"} {
		set mode w
		set eofc ""
	} else {
		set mode r
		set eofc [^Z]
	}
	return [openIt[string totitle $dir] $fn $mode -eofchar $eofc -encoding utf-8 -translation lf]
}

#
# Create or modify a Thatch file
#
proc thatchOp {op ifn ofn args} {
	set if [openItIn $ifn]
	if {$op eq "create"} {
		chan configure $if -eofchar [^Z]
	} else {
		chan configure $if -eofchar ""
	}
	set of [thatchOpen $ofn out]
	chan copy $if $of
	closeIt $if
	foreach fs [ags->fsl $args] {
		fs->fic $of $fs
	}
	closeIt $of
	return 1
}

proc thatchCopyCallbackMain {t fn f fid args} {
	lassign $args fsl of
	puts -nonewline $of [read $f]
	return skip
}

proc thatchCopyCallbackFile {t fn f fid args} {
	lassign $args fsl of

	set dosize 0
	set dobase64 0
	set undobase64 0
	set dozip 0
	set undozip 0
	set ofid $fid
	if {[set i [lsearch -index 0 $fsl [dict get $fid name]]] != -1} {
		if {[lindex $fsl $i [lsearch [fsFields] remove]]} {
			return ""
		}
		foreach fld [list size mtime] {
			set v [lindex $fsl $i [lsearch [fsFields] $fld]]
			if {$v == -1} { continue }
			if {$v == 0 && [dict exists $fid $fld]} {
				set fid [dict remove $fid $fld]
			} elseif {$v == 1} {
				if {$fld eq "size"} {
					set dosize 1
				}
			}
		}
		foreach fld [list base64 zip] {
			set v [lindex $fsl $i [lsearch [fsFields] $fld]]
			if {$v == -1} { continue }
			if {$v == 0} {
				if {![dict exists $fid transforms]} { continue }
				set transforms [dict get $fid transforms]
				if {[set i [lsearch $transforms $fld]] != -1} {
					set transforms [lreplace $transforms $i $i]
				}
				if {$fld eq "base64"} {set undobase64 1}
				if {$fld eq "zip"}    {set undozip 1}
			} elseif {$v == 1} {
				if {[dict exists $fid transforms]} { continue }
				lappend transforms $fld
				if {$fld eq "base64"} {set dobase64 1}
				if {$fld eq "zip"}    {set dozip 1}
			}
			if {[llength $transforms] == 0} {
				set fid [dict remove $fid transforms]
			} else {
				dict set fid transforms $transforms
			}
		}
		set checksums [dgwd {} $fid checksums]
		set sums1 [split $checksums :,]
		foreach fld [list md5 sha256] {
			set v [lindex $fsl $i [lsearch [fsFields] $fld]]
			if {$v == -1} { continue }
			if {$v == 0} {
				if {[set i [lsearch $sums1 $fld]] != -1} {
					set sums1 [lreplace $sums1 $i $i+1]
				}
			} elseif {$v == 1} {
			}
		}
		if {[llength $sums1] == 0} {
			if {[dict exists $fid checksums]} {
				set fid [dict remove $fid checksums]
			}
		} else {
			#dict set fid checksums something
		}
	}

	set d [read $f]

	if {$undobase64} {
		set d [thatchTransform $d decode {*}[dgwd {} $ofid transforms]]
		if {[dict exists $fid stored-size]} {
			set fid [dict remove $fid stored-size]
		}
	}
	if {$undozip} {
		set d [thatchTransform $d decode {*}[dgwd {} $ofid transforms]]
		if {[dict exists $fid stored-size]} {
			set fid [dict remove $fid stored-size]
		}
	}
	if {$dosize} {
		dict set fid size [string length $d]
	}
	if {$dobase64} {
		set d [thatchTransform $d encode {*}[dict get $fid transforms]]
		dict set fid stored-size [string length $d]
	}
	if {$dozip} {
		set d [thatchTransform $d encode {*}[dict get $fid transforms]]
		dict set fid stored-size [string length $d]
	}
	fid->fic $of [dict remove $fid offset]
	puts -nonewline $of $d

	return skip
}

proc thatchCopy {ifn ofn args} {
	set of [thatchOpen $ofn out]
	thatchTraverse $ifn [list [imn thatchCopyCallbackFile] [imn thatchCopyCallbackMain]] [ags->fsl $args] $of
	closeIt $of
	return 1
}

proc thatchNameMatch {fid g} {
	return [string match $g [dict get $fid name]]
}

proc zthatchFullFileGlobCallback {t fn f fid args} {
	variable res
	if {$t == 2} {
		dict set res main [read $f]
		return skip
	}
	foreach a $args {
		if {[thatchNameMatch $fid $a]} {
			dict set res thIndex [dict get $fid name] $fid
		}
	}
	return ""
}

proc zthatchFullFileGlob {fn args} {
	if {[llength $args] == 0} { set args [list *] }
	variable res
	set res [dict create]
	thatchTraverse $fn [list [imn thatchFullFileGlobCallback]] {*}$args
	return $res
}

proc thatchFullFileGlobCallback {t fn f fid args} {
	variable res
	if {$t == 2} {
		set size [string length [read $f]]
		dict set res $fn [dict set fid size $size]
		return skip
	}
	foreach a $args {
		if {[thatchNameMatch $fid $a]} {
			dict set res [dict get $fid name] $fid
		}
	}
	return ""
}

proc thatchFullFileGlob {fn args} {
	if {[llength $args] == 0} { set args [list *] }
	variable res
	set res [dict create]
	thatchTraverse $fn [list [imn thatchFullFileGlobCallback]] {*}$args
	return $res
}

proc thatchFileGlobCallback {t fn f fid args} {
	if {$t == 2} { return "" }
	variable res
	foreach a $args {
		if {[thatchNameMatch $fid $a]} {
			dict set res [dict get $fid name] $fid
		}
	}
	return ""
}

proc thatchFileGlob {fn args} {
	if {[llength $args] == 0} { set args [list *] }
	variable res
	set res [dict create]
	thatchTraverse $fn [list [imn thatchFileGlobCallback]] {*}$args
	return $res
}

proc thatchTraverse {fn cb args} {
	# This is supposed to be a Thatch file so it should conform
	set f [thatchOpen $fn]

	# Setup callbacks
	lassign $cb cb mcb
	if {$mcb eq ""} {
		set mcb $cb
	}

	# Get the 'main'
	set fid [dict create name $fn offset 0]
	set r [$mcb 2 $fn $f $fid {*}$args]
	if {$r ne "skip"} {
		read $f
	}

	# Note its largesse
	set offset [tell $f]

	# Now let's see if there's anything else
	while {1} {
		# We have hit eof so check if it's a ^Z eof or a real eof.
		# Do this by turning off -eofchar detection and reading one char:
		# it should be a ^Z. Set -eofchar back to ^Z after.
		fconfigure $f -eofchar {}
		set cz [read $f 1]
		# Real eof? If so, $cz should also be "".
		if {[eof $f] || $cz eq ""} {
			# Normal case
			if {[eof $f] && $cz eq ""} {
				break
			}
			# todo, strange case
			break
		}
		# Gotta be control-zee
		if {$cz ne [^Z]} { binary scan $cz c c; error "Expected ^Z at $offset, got \"[format %#x $c]\"::[gets $f]" }
		fconfigure $f -eofchar [^Z]
		# After the ^Z should be the sig
		set something [read $f [string length [sig]]]
		if {$something ne [sig]} {
			if {[eof $f]} {
				if {$something eq ""} {
					# null block
					continue
				}
			} else {
				append something [read $f]
			}
			# anon block
			continue
		}
		# Now we should be at the start of the file info line
		set fis [gets $f]
		# Do some checks ...
		if {[eof $f]} { explode }

		# Recalc offset:
		#    ^Z           \n                                 fis                               \n
		incr offset; incr offset [string length [sig]]; incr offset [string length $fis]; incr offset

		set fid [fis->fid $fis]
		dict set fid offset $offset
		set r [$cb 1 $fn $f $fid {*}$args]
		if {$r eq "stop"} { break }
		set size  [dgwd -1 $fid size]
		set ssize [dgwd -1 $fid stored-size]
		if {$ssize > 0} { set size $ssize }
		if {$size == -1} {
			if {$r ne "skip"} {
				read $f
			}
			set offset [tell $f]
		} else {
			if {$r ne "skip"} {
				seek $f $size current
			}
			incr offset $size
		}
	}
	closeIt $f
}

proc thatchExtract {fn fid} {
	set f [thatchOpen $fn]

	set name [lindex [dict keys $fid] 0]
	seek $f [dict get $fid $name offset] start

	set size [dgwd -1 $fid $name size]
	set ssize [dgwd -1 $fid $name stored-size]

	set transforms [dgwd {} $fid $name transforms]
	set checksums [dgwd "" $fid $name checksums]

	if {$ssize < 1} {
		set ssize $size
	}

	if {$ssize > 0} {
		set data [read $f $ssize]
	} else {
		set data [read $f]
	}

	closeIt $f

	set data [thatchTransform $data decode {*}[lreverse $transforms]]

	set checksum_errs [thatchCheckChecksums $data {*}$checksums]
	if {[llength $checksum_errs] > 0} {
		error "checksum mismatches ($fid):\n![join $checksum_errs \n]!"
	}

	return $data
}

proc thatchExtractMain {fn} {
	set f [thatchOpen $fn]
	set data [read $f]
	closeIt $f
	return $data
}

proc thatchIndexGlob {fn args} {
	variable thIndex
	if {[llength $args] == 0} { set args [list *] }
	set res [dict create]
	foreach a $args {
		set res [dict merge $res [dict filter $thIndex key $a]]
	}
	return $res
}

proc thatchCreateIndex {fn} {
	thatchDestroyIndex
	variable thIndex [thatchFileGlob $fn]
	interp alias {} [imn thatchGlob] {} [imn thatchIndexGlob]
}

proc thatchDestroyIndex {} {
	variable thIndex
	unset -nocomplain thIndex
	interp alias {} [imn thatchGlob] {} [imn thatchFileGlob]
}

#-------------------------------------------------------------------
# Overrides
#-------------------------------------------------------------------

proc thatchSourceOverride {fn args} {
	if {[dict size [set fid [thatchGlob $fn {*}$args]]] > 0} {
		set  script [info script]
		info script [lindex [dict keys $fid]]
		set  retval [uplevel 1 [thatchExtract $fn $fid]]]
		info script $script
	} else {
		set retval [uplevel 1 [list ::tcl::tcl_source {*}$args]]
	}
	return $retval
}

proc thatchImageOverride {fn args} {
	if {
		   [llength $args] > 3
		&& [lindex $args 0] eq "create"
		&& [set ind [lsearch $args -file]] != -1
		&& [dict size [set fid [thatchGlob $fn [lindex $args $ind+1]]]] > 0
	} {
		lset args $ind -data
		lset args $ind+1 [thatchExtract $fn $fid]
	}
	return [uplevel 1 [list ::tcl::tcl_image {*}$args]]
}

proc thatchLoadOverride {fn args} {
	set lfi -1
	foreach lfn $args {
		incr lfi
		if {[string index $lfn 0] ne "-"} {
			break
		}
	}
	if {$lfi > -1 && [dict size [set fid [thatchGlob $fn $lfn]]] > 0} {
		set c [file tempfile t thatch]
		chan configure $c -translation binary
		puts -nonewline $c [thatchExtract $fn $fid]
		close $c
		lset args $lfi $t
		if {[llength $args] > ($lfi - 1)} {
			lappend args [string totitle [lindex [regexp -inline {^lib([a-zA-z_]+).*} [file tail $lfn]] end]]
		}
		set code [catch {uplevel 1 [list ::tcl::tcl_load {*}$args]} res]
		file delete -force $t
	} else {
		set code [catch {uplevel 1 [list ::tcl::tcl_load {*}$args]} res]
	}
	return -code $code $res
}

proc thatchFileOverride {fn args} {
	set ok 0
	if {[llength $args] == 2} {
		set fcmd [lindex $args 0]
		if {$fcmd in {exists isfile owned readable executable isdirectory writable atime mtime attributes size type}} {
			set ok 1
		}
	}
	if {[llength $args] == 3} {
		set fcmd [lindex $args 0]
		if {$fcmd in {lstat stat}} {
			set ok 1
		}
	}

	if {[lindex $args 0] eq "type" && [lindex $args 1] eq ""} { return "directory" }
	if {$ok && [dict size [set fid [thatchGlob $fn [lindex $args 1]]]] == 1} {
		switch -exact -- [lindex $args 0] {
		exists -
		isfile -
		owned -
		readable {
			return 1
		}
		executable -
		isdirectory -
		writable {
			return 0
		}
		type {
			return "file"
		}
		atime -
		mtime {
			return [dict get $fid mtime]
		}
		attributes {
			return 0o444
		}
		size {
			return $size
		}
		lstat -
		stat {
			upvar 1 [lindex $args 2] a
			unset -nocomplain a
			array set a [list atime [dict get $fid mtime] ctime [dict get $fid mtime] dev -1 gid -1 ino -1 mode 0o444 mtime [dict get $fid mtime] nlink 1 size [dict get $fid size] type "file" uid -1]
			return ""
		}
		default { explode! }
		}
	}
	return [uplevel 1 [list ::tcl::tcl_file {*}$args]]
}

proc thatchGlobOverride {fn args} {
#puts $fn:$args
#if {[catch {info level -1} e]} { set e :: }
#puts $e:$args
	variable thIndex
	array set g {-join 0 -tails 0 -types {} -directory "" -path "" patterns {}}
	set state opt
	foreach arg $args {
		switch -exact -- $state {
		opt {
			switch -- $arg {
			-join - -tails { set g($arg) 1 }
			-dir - -directory - -path - -types {
				if {$arg eq "-dir"} { set arg "-directory" }
				set state setelem
				set elem $arg
			}
			-nocomplain {}
			-- { set state endopts }
			default { lappend g(patterns) $arg }
			}
		}
		endopts { lappend g(patterns) $arg }
		setelem { set state opt; set g($elem) $arg }
		}
	}
	if {$g(-join)} { set g(patterns) [file join {*}$g(patterns)] }
	set fid [dict create]
	foreach p $g(patterns) {
		set fid [dict merge $fid [thatchGlob $fn [file join $g(-directory) $g(-path) $p]]]
	}
	if {[dict size $fid] > 0} {
		return [dict keys $fid]
	}
	tailcall ::tcl::tcl_glob {*}$args
}

#-------------------------------------------------------------------
# Setup
#-------------------------------------------------------------------

proc overrideAProc {fn proc} {
	if {[llength [info commands ::$proc]]} {
		rename ::$proc ::tcl::tcl_$proc
		interp alias {} ::$proc {} [imn thatch[string totitle $proc]Override] $fn
	} else {
		
	}
}

proc thatchSetup {fn args} {
	set oo {}; foreach o [set op {file glob image load source index packages modules}] { lappend oo -no$o }
	foreach a $args {
		if {[lsearch -exact $oo $a] == -1} {
			error [unknownOption $a $oo]
		}
		set i [lsearch -exact $op [string range $a 3 end]]
		set op [lreplace $op $i $i]
	}
	set createIndex 0
	if {[set i [lsearch -exact $op index]] != -1} {
		set op [lreplace $op $i $i]
		set createIndex 1
	}
	set setupPackages 0
	if {[set i [lsearch -exact $op packages]] != -1} {
		set op [lreplace $op $i $i]
		set setupPackages 1
	}
	set setupModules 0
	if {[set i [lsearch -exact $op modules]] != -1} {
		set op [lreplace $op $i $i]
		set setupModules 1
	}
	foreach p $op { overrideAProc $fn $p }
	if {$createIndex} { thatchCreateIndex $fn }
	if {$setupPackages} {
		dict for {k v} [thatchGlob $fn *pkgIndex.tcl *tclIndex] {
			set ::dir [file dirname $k]
			uplevel #0 [thatchExtract $fn [dict create $k $v]]
		}
		unset -nocomplain ::dir
	}
	if {$setupModules} {
		dict for {k v} [thatchGlob $fn {*-[0-9]*.tm}] {
			if {![regexp -- {^([_[:alpha:]][:_[:alnum:]]*)-([[:digit:]].*)[.]tm$} [file tail $k] -> pn pv]} { continue }
			if {[dict exists $v modbase]} {
				set pn [string map {/ ::} [string trimleft [string range $k [string length [dict get $v modbase]] end-[string length [file tail $k]]] /]]$pn
			}
			package ifneeded $pn $pv "[::list package provide $pn $pv];[::list source -encoding utf-8 $k]"
		}
	}
}

#-------------------------------------------------------------------
# Package Setup
#-------------------------------------------------------------------

proc setup {} {
	package require Tcl 8.5
	aliasconst ^Z \x1a sig "\n# THATCH "
	interp alias {} [imn thatchCreate] {} [imn thatchOp] create
	interp alias {} [imn thatchAdd]    {} [imn thatchOp] add
	thatchDestroyIndex
	namespace export thatch*
	package provide thatch 0.5
}

namespace current}]::setup

# EOF

# THATCH /packages/ctext/ctext.tcl 
# By George Peter Staplin
# See also the README for a list of contributors
# RCS: @(#) $Id: ctext.tcl,v 1.9 2011/04/18 19:49:48 andreas_kupries Exp $

package require Tk
package provide ctext 3.3

namespace eval ctext {}

#win is used as a unique token to create arrays for each ctext instance
proc ctext::getAr {win suffix name} {
    set arName __ctext[set win][set suffix]
    uplevel [list upvar \#0 $arName $name]
    return $arName
}

proc ctext {win args} {
    if {[llength $args] & 1} {
	return -code error \
	    "invalid number of arguments given to ctext (uneven number after window) : $args"
    }

    frame $win -class Ctext

    set tmp [text .__ctextTemp]

    ctext::getAr $win config ar

    set ar(-fg) [$tmp cget -foreground]
    set ar(-bg) [$tmp cget -background]
    set ar(-font) [$tmp cget -font]
    set ar(-relief) [$tmp cget -relief]
    destroy $tmp
    set ar(-yscrollcommand) ""
    set ar(-linemap) 1
    set ar(-linemapfg) $ar(-fg)
    set ar(-linemapbg) $ar(-bg)
    set ar(-linemap_mark_command) {}
    set ar(-linemap_markable) 1
    set ar(-linemap_select_fg) black
    set ar(-linemap_select_bg) yellow
    set ar(-highlight) 1
    set ar(win) $win
    set ar(modified) 0
    set ar(commentsAfterId) ""
    set ar(highlightAfterId) ""
    set ar(blinkAfterId) ""

    set ar(ctextFlags) [list -yscrollcommand -linemap -linemapfg -linemapbg \
			    -font -linemap_mark_command -highlight -linemap_markable \
			    -linemap_select_fg \
			    -linemap_select_bg]

    array set ar $args

    foreach flag {foreground background} short {fg bg} {
	if {[info exists ar(-$flag)] == 1} {
	    set ar(-$short) $ar(-$flag)
	    unset ar(-$flag)
	}
    }

    # Now remove flags that will confuse text and those that need
    # modification:
    foreach arg $ar(ctextFlags) {
	if {[set loc [lsearch $args $arg]] >= 0} {
	    set args [lreplace $args $loc [expr {$loc + 1}]]
	}
    }

    text $win.l -font $ar(-font) -width 1 -height 1 \
	-relief $ar(-relief) -fg $ar(-linemapfg) \
	-bg $ar(-linemapbg) -takefocus 0

    set topWin [winfo toplevel $win]
    bindtags $win.l [list $win.l $topWin all]

    if {$ar(-linemap) == 1} {
	grid $win.l -sticky ns -row 0 -column 0
    }

    set args [concat $args [list -yscrollcommand \
				[list ctext::event:yscroll $win $ar(-yscrollcommand)]]]

    #escape $win, because it could have a space
    eval text \$win.t -font \$ar(-font) $args

    grid $win.t -row 0 -column 1 -sticky news
    grid rowconfigure $win 0 -weight 100
    grid columnconfigure $win 1 -weight 100

    bind $win.t <Configure> [list ctext::linemapUpdate $win]
    bind $win.l <ButtonPress-1> [list ctext::linemapToggleMark $win %y]
    bind $win.t <KeyRelease-Return> [list ctext::linemapUpdate $win]
    rename $win __ctextJunk$win
    rename $win.t $win._t

    bind $win <Destroy> [list ctext::event:Destroy $win %W]
    bindtags $win.t [linsert [bindtags $win.t] 0 $win]

    interp alias {} $win {} ctext::instanceCmd $win
    interp alias {} $win.t {} $win

    # If the user wants C comments they should call
    # ctext::enableComments
    ctext::disableComments $win
    ctext::modified $win 0
    ctext::buildArgParseTable $win

    return $win
}

proc ctext::event:yscroll {win clientData args} {
    ctext::linemapUpdate $win

    if {$clientData == ""} {
	return
    }
    uplevel \#0 $clientData $args
}

proc ctext::event:Destroy {win dWin} {
    if {![string equal $win $dWin]} {
	return
    }

    ctext::getAr $win config configAr

    catch {after cancel $configAr(commentsAfterId)}
    catch {after cancel $configAr(highlightAfterId)}
    catch {after cancel $configAr(blinkAfterId)}

    catch {rename $win {}}
    interp alias {} $win.t {}
    ctext::clearHighlightClasses $win
    array unset [ctext::getAr $win config ar]
}

# This stores the arg table within the config array for each instance.
# It's used by the configure instance command.
proc ctext::buildArgParseTable win {
    set argTable [list]

    lappend argTable any -linemap_mark_command {
	set configAr(-linemap_mark_command) $value
	break
    }

    lappend argTable {1 true yes} -linemap {
	grid $self.l -sticky ns -row 0 -column 0
	grid columnconfigure $self 0 \
	    -minsize [winfo reqwidth $self.l]
	set configAr(-linemap) 1
	break
    }

    lappend argTable {0 false no} -linemap {
	grid forget $self.l
	grid columnconfigure $self 0 -minsize 0
	set configAr(-linemap) 0
	break
    }

    lappend argTable any -yscrollcommand {
	set cmd [list $self._t config -yscrollcommand \
		     [list ctext::event:yscroll $self $value]]

	if {[catch $cmd res]} {
	    return $res
	}
	set configAr(-yscrollcommand) $value
	break
    }

    lappend argTable any -linemapfg {
	if {[catch {winfo rgb $self $value} res]} {
	    return -code error $res
	}
	$self.l config -fg $value
	set configAr(-linemapfg) $value
	break
    }

    lappend argTable any -linemapbg {
	if {[catch {winfo rgb $self $value} res]} {
	    return -code error $res
	}
	$self.l config -bg $value
	set configAr(-linemapbg) $value
	break
    }

    lappend argTable any -font {
	if {[catch {$self.l config -font $value} res]} {
	    return -code error $res
	}
	$self._t config -font $value
	set configAr(-font) $value
	break
    }

    lappend argTable {0 false no} -highlight {
	set configAr(-highlight) 0
	break
    }

    lappend argTable {1 true yes} -highlight {
	set configAr(-highlight) 1
	break
    }

    lappend argTable {0 false no} -linemap_markable {
	set configAr(-linemap_markable) 0
	break
    }

    lappend argTable {1 true yes} -linemap_markable {
	set configAr(-linemap_markable) 1
	break
    }

    lappend argTable any -linemap_select_fg {
	if {[catch {winfo rgb $self $value} res]} {
	    return -code error $res
	}
	set configAr(-linemap_select_fg) $value
	$self.l tag configure lmark -foreground $value
	break
    }

    lappend argTable any -linemap_select_bg {
	if {[catch {winfo rgb $self $value} res]} {
	    return -code error $res
	}
	set configAr(-linemap_select_bg) $value
	$self.l tag configure lmark -background $value
	break
    }

    ctext::getAr $win config ar
    set ar(argTable) $argTable
}

proc ctext::commentsAfterIdle {win} {
    ctext::getAr $win config configAr

    if {"" eq $configAr(commentsAfterId)} {
	set configAr(commentsAfterId) [after idle \
	   [list ctext::comments $win [set afterTriggered 1]]]
    }
}

proc ctext::highlightAfterIdle {win lineStart lineEnd} {
    ctext::getAr $win config configAr

    if {"" eq $configAr(highlightAfterId)} {
	set configAr(highlightAfterId) [after idle \
	    [list ctext::highlight $win $lineStart $lineEnd [set afterTriggered 1]]]
    }
}

proc ctext::instanceCmd {self cmd args} {
    #slightly different than the RE used in ctext::comments
    set commentRE {\"|\\|'|/|\*}

    switch -glob -- $cmd {
	append {
	    if {[catch {$self._t get sel.first sel.last} data] == 0} {
		clipboard append -displayof $self $data
	    }
	}

	cget {
	    set arg [lindex $args 0]
	    ctext::getAr $self config configAr

	    foreach flag $configAr(ctextFlags) {
		if {[string match ${arg}* $flag]} {
		    return [set configAr($flag)]
		}
	    }
	    return [$self._t cget $arg]
	}

	conf* {
	    ctext::getAr $self config configAr

	    if {0 == [llength $args]} {
		set res [$self._t configure]
		set del [lsearch -glob $res -yscrollcommand*]
		set res [lreplace $res $del $del]
		foreach flag $configAr(ctextFlags) {
		    lappend res [list $flag [set configAr($flag)]]
		}
		return $res
	    }

	    array set flags {}
	    foreach flag $configAr(ctextFlags) {
		set loc [lsearch $args $flag]
		if {$loc < 0} {
		    continue
		}

		if {[llength $args] <= ($loc + 1)} {
		    #.t config -flag
		    return [set configAr($flag)]
		}

		set flagArg [lindex $args [expr {$loc + 1}]]
		set args [lreplace $args $loc [expr {$loc + 1}]]
		set flags($flag) $flagArg
	    }

	    foreach {valueList flag cmd} $configAr(argTable) {
		if {[info exists flags($flag)]} {
		    foreach valueToCheckFor $valueList {
			set value [set flags($flag)]
			if {[string equal "any" $valueToCheckFor]} $cmd \
			    elseif {[string equal $valueToCheckFor [set flags($flag)]]} $cmd
		    }
		}
	    }

	    if {[llength $args]} {
		#we take care of configure without args at the top of this branch
		uplevel 1 [linsert $args 0 $self._t configure]
	    }
	}

	copy {
	    tk_textCopy $self
	}

	cut {
	    if {[catch {$self.t get sel.first sel.last} data] == 0} {
		clipboard clear -displayof $self.t
		clipboard append -displayof $self.t $data
		$self delete [$self.t index sel.first] [$self.t index sel.last]
		ctext::modified $self 1
	    }
	}

	delete {
	    #delete n.n ?n.n

	    set argsLength [llength $args]

	    #first deal with delete n.n
	    if {$argsLength == 1} {
		set deletePos [lindex $args 0]
		set prevChar [$self._t get $deletePos]

		$self._t delete $deletePos
		set char [$self._t get $deletePos]

		set prevSpace [ctext::findPreviousSpace $self._t $deletePos]
		set nextSpace [ctext::findNextSpace $self._t $deletePos]

		set lineStart [$self._t index "$deletePos linestart"]
		set lineEnd [$self._t index "$deletePos + 1 chars lineend"]

		#This pattern was used in 3.1.  We may want to investigate using it again
		#eventually to reduce flicker.  It caused a bug with some patterns.
		#if {[string equal $prevChar "#"] || [string equal $char "#"]} {
		#	set removeStart $lineStart
		#	set removeEnd $lineEnd
		#} else {
		#	set removeStart $prevSpace
		#	set removeEnd $nextSpace
		#}
		set removeStart $lineStart
		set removeEnd $lineEnd

		foreach tag [$self._t tag names] {
		    if {[string equal $tag "_cComment"] != 1} {
			$self._t tag remove $tag $removeStart $removeEnd
		    }
		}

		set checkStr "$prevChar[set char]"

		if {[regexp $commentRE $checkStr]} {
		    ctext::commentsAfterIdle $self
		}

		ctext::highlightAfterIdle $self $lineStart $lineEnd
		ctext::linemapUpdate $self
	    } elseif {$argsLength == 2} {
		#now deal with delete n.n ?n.n?
		set deleteStartPos [lindex $args 0]
		set deleteEndPos [lindex $args 1]

		set data [$self._t get $deleteStartPos $deleteEndPos]

		set lineStart [$self._t index "$deleteStartPos linestart"]
		set lineEnd [$self._t index "$deleteEndPos + 1 chars lineend"]
		eval \$self._t delete $args

		foreach tag [$self._t tag names] {
		    if {[string equal $tag "_cComment"] != 1} {
			$self._t tag remove $tag $lineStart $lineEnd
		    }
		}

		if {[regexp $commentRE $data]} {
		    ctext::commentsAfterIdle $self
		}

		ctext::highlightAfterIdle $self $lineStart $lineEnd
		if {[string first "\n" $data] >= 0} {
		    ctext::linemapUpdate $self
		}
	    } else {
		return -code error "invalid argument(s) sent to $self delete: $args"
	    }
	    ctext::modified $self 1
	}

	fastdelete {
	    eval \$self._t delete $args
	    ctext::modified $self 1
	    ctext::linemapUpdate $self
	}

	fastinsert {
	    eval \$self._t insert $args
	    ctext::modified $self 1
	    ctext::linemapUpdate $self
	}

	highlight {
	    ctext::highlight $self [lindex $args 0] [lindex $args 1]
	    ctext::comments $self
	}

	insert {
	    if {[llength $args] < 2} {
		return -code error "please use at least 2 arguments to $self insert"
	    }

	    set insertPos [lindex $args 0]
	    set prevChar [$self._t get "$insertPos - 1 chars"]
	    set nextChar [$self._t get $insertPos]
	    set lineStart [$self._t index "$insertPos linestart"]
	    set prevSpace [ctext::findPreviousSpace $self._t ${insertPos}-1c]
	    set data [lindex $args 1]
	    eval \$self._t insert $args

	    set nextSpace [ctext::findNextSpace $self._t insert]
	    set lineEnd [$self._t index "insert lineend"]

	    if {[$self._t compare $prevSpace < $lineStart]} {
		set prevSpace $lineStart
	    }

	    if {[$self._t compare $nextSpace > $lineEnd]} {
		set nextSpace $lineEnd
	    }

	    foreach tag [$self._t tag names] {
		if {[string equal $tag "_cComment"] != 1} {
		    $self._t tag remove $tag $prevSpace $nextSpace
		}
	    }

	    set REData $prevChar
	    append REData $data
	    append REData $nextChar
	    if {[regexp $commentRE $REData]} {
		ctext::commentsAfterIdle $self
	    }

	    ctext::highlightAfterIdle $self $lineStart $lineEnd

	    switch -- $data {
		"\}" {
		    ctext::matchPair $self "\\\{" "\\\}" "\\"
		}
		"\]" {
		    ctext::matchPair $self "\\\[" "\\\]" "\\"
		}
		"\)" {
		    ctext::matchPair $self "\\(" "\\)" ""
		}
		"\"" {
		    ctext::matchQuote $self
		}
	    }
	    ctext::modified $self 1
	    ctext::linemapUpdate $self
	}

	paste {
	    tk_textPaste $self
	    ctext::modified $self 1
	}

	edit {
	    set subCmd [lindex $args 0]
	    set argsLength [llength $args]

	    ctext::getAr $self config ar

	    if {"modified" == $subCmd} {
		if {$argsLength == 1} {
		    return $ar(modified)
		} elseif {$argsLength == 2} {
		    set value [lindex $args 1]
		    set ar(modified) $value
		} else {
		    return -code error "invalid arg(s) to $self edit modified: $args"
		}
	    } else {
		#Tk 8.4 has other edit subcommands that I don't want to emulate.
		return [uplevel 1 [linsert $args 0 $self._t $cmd]]
	    }
	}

	default {
	    return [uplevel 1 [linsert $args 0 $self._t $cmd]]
	}
    }
}

proc ctext::tag:blink {win count {afterTriggered 0}} {
    if {$count & 1} {
	$win tag configure __ctext_blink \
	    -foreground [$win cget -bg] -background [$win cget -fg]
    } else {
	$win tag configure __ctext_blink \
	    -foreground [$win cget -fg] -background [$win cget -bg]
    }

    ctext::getAr $win config configAr
    if {$afterTriggered} {
	set configAr(blinkAfterId) ""
    }

    if {$count == 4} {
	$win tag delete __ctext_blink 1.0 end
	return
    }

    incr count
    if {"" eq $configAr(blinkAfterId)} {
	set configAr(blinkAfterId) [after 50 \
		[list ctext::tag:blink $win $count [set afterTriggered 1]]]
    }
}

proc ctext::matchPair {win str1 str2 escape} {
    set prevChar [$win get "insert - 2 chars"]

    if {[string equal $prevChar $escape]} {
	#The char that we thought might be the end is actually escaped.
	return
    }

    set searchRE "[set str1]|[set str2]"
    set count 1

    set pos [$win index "insert - 1 chars"]
    set endPair $pos
    set lastFound ""
    while 1 {
	set found [$win search -backwards -regexp $searchRE $pos]

	if {$found == "" || [$win compare $found > $pos]} {
	    return
	}

	if {$lastFound != "" && [$win compare $found == $lastFound]} {
	    #The search wrapped and found the previous search
	    return
	}

	set lastFound $found
	set char [$win get $found]
	set prevChar [$win get "$found - 1 chars"]
	set pos $found

	if {[string equal $prevChar $escape]} {
	    continue
	} elseif {[string equal $char [subst $str2]]} {
	    incr count
	} elseif {[string equal $char [subst $str1]]} {
	    incr count -1
	    if {$count == 0} {
		set startPair $found
		break
	    }
	} else {
	    # This shouldn't happen.  I may in the future make it
	    # return -code error
	    puts stderr "ctext seems to have encountered a bug in ctext::matchPair"
	    return
	}
    }

    $win tag add __ctext_blink $startPair
    $win tag add __ctext_blink $endPair
    ctext::tag:blink $win 0
}

proc ctext::matchQuote {win} {
    set endQuote [$win index insert]
    set start [$win index "insert - 1 chars"]

    if {[$win get "$start - 1 chars"] == "\\"} {
	#the quote really isn't the end
	return
    }
    set lastFound ""
    while 1 {
	set startQuote [$win search -backwards \" $start]
	if {$startQuote == "" || [$win compare $startQuote > $start]} {
	    #The search found nothing or it wrapped.
	    return
	}

	if {$lastFound != "" && [$win compare $lastFound == $startQuote]} {
	    #We found the character we found before, so it wrapped.
	    return
	}
	set lastFound $startQuote
	set start [$win index "$startQuote - 1 chars"]
	set prevChar [$win get $start]

	if {$prevChar == "\\"} {
	    continue
	}
	break
    }

    if {[$win compare $endQuote == $startQuote]} {
	#probably just \"
	return
    }

    $win tag add __ctext_blink $startQuote $endQuote
    ctext::tag:blink $win 0
}

proc ctext::enableComments {win} {
    $win tag configure _cComment -foreground khaki
}
proc ctext::disableComments {win} {
    catch {$win tag delete _cComment}
}

proc ctext::comments {win {afterTriggered 0}} {
    if {[catch {$win tag cget _cComment -foreground}]} {
	#C comments are disabled
	return
    }

    if {$afterTriggered} {
	ctext::getAr $win config configAr
	set configAr(commentsAfterId) ""
    }

    set startIndex 1.0
    set commentRE {\\\\|\"|\\\"|\\'|'|/\*|\*/}
    set commentStart 0
    set isQuote 0
    set isSingleQuote 0
    set isComment 0
    $win tag remove _cComment 1.0 end
    while 1 {
	set index [$win search -count length -regexp $commentRE $startIndex end]

	if {$index == ""} {
	    break
	}

	set endIndex [$win index "$index + $length chars"]
	set str [$win get $index $endIndex]
	set startIndex $endIndex

	if {$str == "\\\\"} {
	    continue
	} elseif {$str == "\\\""} {
	    continue
	} elseif {$str == "\\'"} {
	    continue
	} elseif {$str == "\"" && $isComment == 0 && $isSingleQuote == 0} {
	    if {$isQuote} {
		set isQuote 0
	    } else {
		set isQuote 1
	    }
	} elseif {$str == "'" && $isComment == 0 && $isQuote == 0} {
	    if {$isSingleQuote} {
		set isSingleQuote 0
	    } else {
		set isSingleQuote 1
	    }
	} elseif {$str == "/*" && $isQuote == 0 && $isSingleQuote == 0} {
	    if {$isComment} {
		#comment in comment
		break
	    } else {
		set isComment 1
		set commentStart $index
	    }
	} elseif {$str == "*/" && $isQuote == 0 && $isSingleQuote == 0} {
	    if {$isComment} {
		set isComment 0
		$win tag add _cComment $commentStart $endIndex
		$win tag raise _cComment
	    } else {
		#comment end without beginning
		break
	    }
	}
    }
}

proc ctext::addHighlightClass {win class color keywords} {
    set ref [ctext::getAr $win highlight ar]
    foreach word $keywords {
	set ar($word) [list $class $color]
    }
    $win tag configure $class

    ctext::getAr $win classes classesAr
    set classesAr($class) [list $ref $keywords]
}

#For [ ] { } # etc.
proc ctext::addHighlightClassForSpecialChars {win class color chars} {
    set charList [split $chars ""]

    set ref [ctext::getAr $win highlightSpecialChars ar]
    foreach char $charList {
	set ar($char) [list $class $color]
    }
    $win tag configure $class

    ctext::getAr $win classes classesAr
    set classesAr($class) [list $ref $charList]
}

proc ctext::addHighlightClassForRegexp {win class color re} {
    set ref [ctext::getAr $win highlightRegexp ar]

    set ar($class) [list $re $color]
    $win tag configure $class

    ctext::getAr $win classes classesAr
    set classesAr($class) [list $ref $class]
}

#For things like $blah
proc ctext::addHighlightClassWithOnlyCharStart {win class color char} {
    set ref [ctext::getAr $win highlightCharStart ar]

    set ar($char) [list $class $color]
    $win tag configure $class

    ctext::getAr $win classes classesAr
    set classesAr($class) [list $ref $char]
}

proc ctext::deleteHighlightClass {win classToDelete} {
    ctext::getAr $win classes classesAr

    if {![info exists classesAr($classToDelete)]} {
	return -code error "$classToDelete doesn't exist"
    }

    foreach {ref keyList} [set classesAr($classToDelete)] {
	upvar #0 $ref refAr
	foreach key $keyList {
	    if {![info exists refAr($key)]} {
		continue
	    }
	    unset refAr($key)
	}
    }
    unset classesAr($classToDelete)
}

proc ctext::getHighlightClasses win {
    ctext::getAr $win classes classesAr

    array names classesAr
}

proc ctext::findNextChar {win index char} {
    set i [$win index "$index + 1 chars"]
    set lineend [$win index "$i lineend"]
    while 1 {
	set ch [$win get $i]
	if {[$win compare $i >= $lineend]} {
	    return ""
	}
	if {$ch == $char} {
	    return $i
	}
	set i [$win index "$i + 1 chars"]
    }
}

proc ctext::findNextSpace {win index} {
    set i [$win index $index]
    set lineStart [$win index "$i linestart"]
    set lineEnd [$win index "$i lineend"]
    #Sometimes the lineend fails (I don't know why), so add 1 and try again.
    if {[$win compare $lineEnd == $lineStart]} {
	set lineEnd [$win index "$i + 1 chars lineend"]
    }

    while {1} {
	set ch [$win get $i]

	if {[$win compare $i >= $lineEnd]} {
	    set i $lineEnd
	    break
	}

	if {[string is space $ch]} {
	    break
	}
	set i [$win index "$i + 1 chars"]
    }
    return $i
}

proc ctext::findPreviousSpace {win index} {
    set i [$win index $index]
    set lineStart [$win index "$i linestart"]
    while {1} {
	set ch [$win get $i]

	if {[$win compare $i <= $lineStart]} {
	    set i $lineStart
	    break
	}

	if {[string is space $ch]} {
	    break
	}

	set i [$win index "$i - 1 chars"]
    }
    return $i
}

proc ctext::clearHighlightClasses {win} {
    #no need to catch, because array unset doesn't complain
    #puts [array exists ::ctext::highlight$win]

    ctext::getAr $win highlight ar
    array unset ar

    ctext::getAr $win highlightSpecialChars ar
    array unset ar

    ctext::getAr $win highlightRegexp ar
    array unset ar

    ctext::getAr $win highlightCharStart ar
    array unset ar

    ctext::getAr $win classes ar
    array unset ar
}

#This is a proc designed to be overwritten by the user.
#It can be used to update a cursor or animation while
#the text is being highlighted.
proc ctext::update {} {

}

proc ctext::highlight {win start end {afterTriggered 0}} {
    ctext::getAr $win config configAr

    if {$afterTriggered} {
	set configAr(highlightAfterId) ""
    }

    if {!$configAr(-highlight)} {
	return
    }

    set si $start
    set twin "$win._t"

    #The number of times the loop has run.
    set numTimesLooped 0
    set numUntilUpdate 600

    ctext::getAr $win highlight highlightAr
    ctext::getAr $win highlightSpecialChars highlightSpecialCharsAr
    ctext::getAr $win highlightRegexp highlightRegexpAr
    ctext::getAr $win highlightCharStart highlightCharStartAr

    while 1 {
	set res [$twin search -count length -regexp -- {([^\s\(\{\[\}\]\)\.\t\n\r;\"'\|,]+)} $si $end]
	if {$res == ""} {
	    break
	}

	set wordEnd [$twin index "$res + $length chars"]
	set word [$twin get $res $wordEnd]
	set firstOfWord [string index $word 0]

	if {[info exists highlightAr($word)] == 1} {
	    set wordAttributes [set highlightAr($word)]
	    foreach {tagClass color} $wordAttributes break

	    $twin tag add $tagClass $res $wordEnd
	    $twin tag configure $tagClass -foreground $color

	} elseif {[info exists highlightCharStartAr($firstOfWord)] == 1} {
	    set wordAttributes [set highlightCharStartAr($firstOfWord)]
	    foreach {tagClass color} $wordAttributes break

	    $twin tag add $tagClass $res $wordEnd
	    $twin tag configure $tagClass -foreground $color
	}
	set si $wordEnd

	incr numTimesLooped
	if {$numTimesLooped >= $numUntilUpdate} {
	    ctext::update
	    set numTimesLooped 0
	}
    }

    foreach {ichar tagInfo} [array get highlightSpecialCharsAr] {
	set si $start
	foreach {tagClass color} $tagInfo break

	while 1 {
	    set res [$twin search -- $ichar $si $end]
	    if {"" == $res} {
		break
	    }
	    set wordEnd [$twin index "$res + 1 chars"]

	    $twin tag add $tagClass $res $wordEnd
	    $twin tag configure $tagClass -foreground $color
	    set si $wordEnd

	    incr numTimesLooped
	    if {$numTimesLooped >= $numUntilUpdate} {
		ctext::update
		set numTimesLooped 0
	    }
	}
    }

    foreach {tagClass tagInfo} [array get highlightRegexpAr] {
	set si $start
	foreach {re color} $tagInfo break
	while 1 {
	    set res [$twin search -count length -regexp -- $re $si $end]
	    if {"" == $res} {
		break
	    }

	    set wordEnd [$twin index "$res + $length chars"]
	    $twin tag add $tagClass $res $wordEnd
	    $twin tag configure $tagClass -foreground $color
	    set si $wordEnd

	    incr numTimesLooped
	    if {$numTimesLooped >= $numUntilUpdate} {
		ctext::update
		set numTimesLooped 0
	    }
	}
    }
}

proc ctext::linemapToggleMark {win y} {
    ctext::getAr $win config configAr

    if {!$configAr(-linemap_markable)} {
	return
    }

    set markChar [$win.l index @0,$y]
    set lineSelected [lindex [split $markChar .] 0]
    set line [$win.l get $lineSelected.0 $lineSelected.end]

    if {$line == ""} {
	return
    }

    ctext::getAr $win linemap linemapAr

    if {[info exists linemapAr($line)] == 1} {
	#It's already marked, so unmark it.
	array unset linemapAr $line
	ctext::linemapUpdate $win
	set type unmarked
    } else {
	#This means that the line isn't toggled, so toggle it.
	array set linemapAr [list $line {}]
	$win.l tag add lmark $markChar [$win.l index "$markChar lineend"]
	$win.l tag configure lmark -foreground $configAr(-linemap_select_fg) \
	    -background $configAr(-linemap_select_bg)
	set type marked
    }

    if {[string length $configAr(-linemap_mark_command)]} {
	uplevel #0 [linsert $configAr(-linemap_mark_command) end $win $type $line]
    }
}

#args is here because -yscrollcommand may call it
proc ctext::linemapUpdate {win args} {
    if {[winfo exists $win.l] != 1} {
	return
    }

    set pixel 0
    set lastLine {}
    set lineList [list]
    set fontMetrics [font metrics [$win._t cget -font]]
    set incrBy [expr {1 + ([lindex $fontMetrics 5] / 2)}]

    while {$pixel < [winfo height $win.l]} {
	set idx [$win._t index @0,$pixel]

	if {$idx != $lastLine} {
	    set line [lindex [split $idx .] 0]
	    set lastLine $idx
	    lappend lineList $line
	}
	incr pixel $incrBy
    }

    ctext::getAr $win linemap linemapAr

    $win.l delete 1.0 end
    set lastLine {}
    foreach line $lineList {
	if {$line == $lastLine} {
	    $win.l insert end "\n"
	} else {
	    if {[info exists linemapAr($line)]} {
		$win.l insert end "$line\n" lmark
	    } else {
		$win.l insert end "$line\n"
	    }
	}
	set lastLine $line
    }
    if {[llength $lineList] > 0} {
	linemapUpdateOffset $win $lineList
    }
    set endrow [lindex [split [$win._t index end-1c] .] 0]
    $win.l configure -width [string length $endrow]
}

# Starting with Tk 8.5 the text widget allows smooth scrolling; this
# code calculates the offset for the line numbering text widget and
# scrolls by the specified amount of pixels

if {![catch {
    package require Tk 8.5
}]} {
    proc ctext::linemapUpdateOffset {win lineList} {
	# reset view for line numbering widget
	$win.l yview 0.0

	# find the first line that is visible and calculate the
	# corresponding line in the line numbers widget
	set lline 1
	foreach line $lineList {
	    set tystart [lindex [$win.t bbox $line.0] 1]
	    if {$tystart != ""} {
		break
	    }
	    incr lline
	}

	# return in case the line numbers text widget is not up to
	# date
	if {[catch {
	    set lystart [lindex [$win.l bbox $lline.0] 1]
	}]} {
	    return
	}

	# return in case the bbox for any of the lines returned an
	# empty value
	if {($tystart == "") || ($lystart == "")} {
	    return
	}

	# calculate the offset and then scroll by specified number of
	# pixels
	set offset [expr {$lystart - $tystart}]
	$win.l yview scroll $offset pixels
    }
}  else  {
    # Do not try to perform smooth scrolling if Tk is 8.4 or less.
    proc ctext::linemapUpdateOffset {args} {}
}

proc ctext::modified {win value} {
    ctext::getAr $win config ar
    set ar(modified) $value
    event generate $win <<Modified>>
    return $value
}

# THATCH /packages/ctext/pkgIndex.tcl 
package ifneeded ctext 3.3 [list source [file join $dir ctext.tcl]]

# THATCH /packages/arc/arc.tcl 
#  Copyright (c) 2015 Sergei Golovan <sgolovan@nes.ru>
#  Derived from https://github.com/horst3180/arc-theme/ under the GNU GPLv3
#  Thus this is available under GNU GPLv3 also, as described in LICENSE

namespace eval ttk::theme::arc {

    variable colors
    array set colors {
        -fg             "#5c616c"
        -bg             "#f5f6f7"
        -disabledbg     "#fbfcfc"
        -disabledfg     "#a9acb2"
        -selectbg       "#5294e2"
        -selectfg       "#ffffff"
        -window         "#ffffff"
        -focuscolor     "#5c616c"
        -checklight     "#fbfcfc"
    }

    proc LoadImages {imgdir} {
        variable I
        foreach file [glob -directory $imgdir *.png] {
            set img [file tail [file rootname $file]]
            set I($img) [image create photo -file $file -format png]
        }
    }

    LoadImages [file join [file dirname [info script]] arc]

    ttk::style theme create arc -parent default -settings {
        ttk::style configure . \
            -background $colors(-bg) \
            -foreground $colors(-fg) \
            -troughcolor $colors(-bg) \
            -selectbg $colors(-selectbg) \
            -selectfg $colors(-selectfg) \
            -fieldbg $colors(-window) \
            -font TkDefaultFont \
            -borderwidth 1 \
            -focuscolor $colors(-focuscolor)

        ttk::style map . -foreground [list disabled $colors(-disabledfg)]

        # Layouts
        ttk::style layout TButton {
            Button.button -children {
                Button.focus -children {
                    Button.padding -children {
                        Button.label -side left -expand true
                    }
                }
            }
        }

        ttk::style layout Toolbutton {
            Toolbutton.button -children {
                Toolbutton.focus -children {
                    Toolbutton.padding -children {
                        Toolbutton.label -side left -expand true
                    }
                }
            }
        }

        ttk::style layout Vertical.TScrollbar {
            Vertical.Scrollbar.trough -sticky ns -children {
                Vertical.Scrollbar.thumb -expand true
            }
        }

        ttk::style layout Horizontal.TScrollbar {
            Horizontal.Scrollbar.trough -sticky ew -children {
                Horizontal.Scrollbar.thumb -expand true
            }
        }

        ttk::style layout TMenubutton {
            Menubutton.button -children {
                Menubutton.focus -children {
                    Menubutton.padding -children {
                        Menubutton.indicator -side right
                        Menubutton.label -side right -expand true
                    }
                }
            }
        }

        ttk::style layout TCombobox {
            Combobox.field -sticky nswe -children {
                Combobox.downarrow -side right -sticky ns -children {
                    Combobox.arrow -side right
                }
                Combobox.padding -expand true -sticky nswe -children {
                    Combobox.textarea -sticky nswe
                }
            }
        }

        ttk::style layout TSpinbox {
            Spinbox.field -side top -sticky we -children {
                Spinbox.buttons -side right -children {
                    null -side right -sticky {} -children {
                        Spinbox.uparrow -side top -sticky nse -children {
                            Spinbox.symuparrow -side right -sticky e
                        }
                        Spinbox.downarrow -side bottom -sticky nse -children {
                            Spinbox.symdownarrow -side right -sticky e
                        }
                    }
                }
                Spinbox.padding -sticky nswe -children {
                    Spinbox.textarea -sticky nswe
                }
            }
        }

        # Elements
        ttk::style element create Button.button image [list $I(button) \
                pressed     $I(button-active) \
                active      $I(button-hover) \
                disabled    $I(button-insensitive) \
            ] -border 3 -padding {3 2} -sticky ewns

        ttk::style element create Toolbutton.button image [list $I(button-empty) \
                selected            $I(button-active) \
                pressed             $I(button-active) \
                {active !disabled}  $I(button-hover) \
            ] -border 3 -padding {3 2} -sticky news

        ttk::style element create Checkbutton.indicator image [list $I(checkbox-unchecked) \
                disabled            $I(checkbox-unchecked-insensitive) \
                {active selected}   $I(checkbox-checked) \
                {pressed selected}  $I(checkbox-checked) \
                active              $I(checkbox-unchecked) \
                selected            $I(checkbox-checked) \
                {disabled selected} $I(checkbox-checked-insensitive) \
            ] -width 22 -sticky w

        ttk::style element create Radiobutton.indicator image [list $I(radio-unchecked) \
                disabled            $I(radio-unchecked-insensitive) \
                {active selected}   $I(radio-checked) \
                {pressed selected}  $I(radio-checked) \
                active              $I(radio-unchecked) \
                selected            $I(radio-checked) \
                {disabled selected} $I(radio-checked-insensitive) \
            ] -width 22 -sticky w

        ttk::style element create Horizontal.Scrollbar.trough image $I(trough-scrollbar-horiz)
        ttk::style element create Horizontal.Scrollbar.thumb \
            image [list $I(slider-horiz) \
                        {pressed !disabled} $I(slider-horiz-active) \
                        {active !disabled}  $I(slider-horiz-prelight) \
                        disabled            $I(slider-horiz-insens) \
            ] -border 6 -sticky ew

        ttk::style element create Vertical.Scrollbar.trough image $I(trough-scrollbar-vert)
        ttk::style element create Vertical.Scrollbar.thumb \
            image [list $I(slider-vert) \
                        {pressed !disabled} $I(slider-vert-active) \
                        {active !disabled}  $I(slider-vert-prelight) \
                        disabled            $I(slider-vert-insens) \
            ] -border 6 -sticky ns

        ttk::style element create Horizontal.Scale.trough \
            image [list $I(trough-horizontal-active) disabled $I(trough-horizontal)] \
            -border {8 5 8 5} -padding 0
        ttk::style element create Horizontal.Scale.slider \
            image [list $I(slider) disabled $I(slider-insensitive) active $I(slider-prelight)] \
            -sticky {}

        ttk::style element create Vertical.Scale.trough \
            image [list $I(trough-vertical-active) disabled $I(trough-vertical)] \
            -border {5 8 5 8} -padding 0
        ttk::style element create Vertical.Scale.slider \
            image [list $I(slider) disabled $I(slider-insensitive) active $I(slider-prelight)] \
            -sticky {}

        ttk::style element create Entry.field \
            image [list $I(entry-border-bg-solid) \
                        focus $I(entry-border-active-bg-solid) \
                        disabled $I(entry-border-disabled-bg)] \
            -border 3 -padding {6 4} -sticky news

        ttk::style element create Labelframe.border image $I(labelframe) \
            -border 4 -padding 4 -sticky news

        ttk::style element create Menubutton.button \
            image [list $I(button) \
                        pressed  $I(button-active) \
                        active   $I(button-hover) \
                        disabled $I(button-insensitive) \
            ] -sticky news -border 3 -padding {3 2}
        ttk::style element create Menubutton.indicator \
            image [list $I(arrow-down) \
                        active   $I(arrow-down-prelight) \
                        pressed  $I(arrow-down-prelight) \
                        disabled $I(arrow-down-insens) \
            ] -sticky e -width 20

        ttk::style element create Combobox.field \
            image [list $I(combo-entry) \
                {readonly disabled}  $I(button-insensitive) \
                {readonly pressed}   $I(button-active) \
                {readonly focus}     $I(button-focus) \
                {readonly hover}     $I(button-hover) \
                readonly             $I(button) \
                {disabled} $I(combo-entry-insensitive) \
                {focus}    $I(combo-entry-focus) \
                {hover}    $I(combo-entry) \
            ] -border 4 -padding {6 0 0 0}
        ttk::style element create Combobox.downarrow \
            image [list $I(combo-entry-button) \
                        pressed   $I(combo-entry-button-active) \
                        active    $I(combo-entry-button-hover) \
                        disabled  $I(combo-entry-button-insensitive) \
          ] -border 4 -padding {0 10 6 10}
        ttk::style element create Combobox.arrow \
            image [list $I(arrow-down) \
                        active    $I(arrow-down-prelight) \
                        pressed   $I(arrow-down-prelight) \
                        disabled  $I(arrow-down-insens) \
          ]  -sticky e -width 15

        ttk::style element create Spinbox.field \
            image [list $I(combo-entry) focus $I(combo-entry-focus)] \
            -border 4 -padding {6 0 0 0} -sticky news
        ttk::style element create Spinbox.uparrow \
            image [list $I(up-background) \
                        pressed   $I(up-background-active) \
                        active    $I(up-background-hover) \
                        disabled  $I(up-background-disable) \
            ] -width 20 -border {0 2 3 0} -padding {0 5 6 2}
        ttk::style element create Spinbox.symuparrow \
            image [list $I(arrow-up-small) \
                        active    $I(arrow-up-small-prelight) \
                        pressed   $I(arrow-up-small-prelight) \
                        disabled  $I(arrow-up-small-insens) \
            ]
        ttk::style element create Spinbox.downarrow \
            image [list $I(down-background) \
                        pressed   $I(down-background-active) \
                        active    $I(down-background-hover) \
                        disabled  $I(down-background-disable) \
            ] -width 20 -border {0 0 3 2} -padding {0 2 6 5}
        ttk::style element create Spinbox.symdownarrow \
            image [list $I(arrow-down-small) \
                        active    $I(arrow-down-small-prelight) \
                        pressed   $I(arrow-down-small-prelight) \
                        disabled  $I(arrow-down-small-insens) \
          ]

        ttk::style element create Notebook.client \
            image $I(notebook) -border 1
        ttk::style element create Notebook.tab \
            image [list $I(tab-top) \
                        selected    $I(tab-top-active) \
                        active      $I(tab-top-hover) \
            ] -padding {0 2 0 0} -border 2

        ttk::style element create Horizontal.Progressbar.trough \
            image $I(trough-progressbar_v) -border {5 1 5 1} -padding 1 -sticky ew
        ttk::style element create Horizontal.Progressbar.pbar \
            image $I(progressbar_v) -border {4 0 4 0} -sticky ew

        ttk::style element create Vertical.Progressbar.trough \
            image $I(trough-progressbar) -border {1 5 1 5} -padding 1 -sticky ns
        ttk::style element create Vertical.Progressbar.pbar \
            image $I(progressbar) -border {0 4 0 4} -sticky ns

        ttk::style element create Treeview.field \
            image $I(treeview) -border 1
        ttk::style element create Treeheading.cell \
            image [list $I(notebook) pressed $I(notebook)] \
            -border 1 -padding 4 -sticky ewns

        ttk::style element create Treeitem.indicator \
            image [list $I(plus) user2 $I(empty) user1 $I(minus)] \
            -width 15 -sticky w

        #ttk::style element create Separator.separator image $I()

        #
        # Settings:
        #

        ttk::style configure TButton -padding {8 4 8 4} -width -10 -anchor center
        ttk::style configure TMenubutton -padding {8 4 4 4}
        ttk::style configure Toolbutton -anchor center
        ttk::style map TCheckbutton -background [list active $colors(-checklight)]
        ttk::style configure TCheckbutton -padding 3
        ttk::style map TRadiobutton -background [list active $colors(-checklight)]
        ttk::style configure TRadiobutton -padding 3
        ttk::style configure TNotebook -tabmargins {0 2 0 0}
        ttk::style configure TNotebook.Tab -padding {6 2 6 2} -expand {0 0 2}
        ttk::style map TNotebook.Tab -expand [list selected {1 2 4 2}]
        ttk::style configure TSeparator -background $colors(-bg)

        # Treeview
        ttk::style configure Treeview -background $colors(-window)
        ttk::style configure Treeview.Item -padding {2 0 0 0}
        ttk::style map Treeview \
            -background [list selected $colors(-selectbg)] \
            -foreground [list selected $colors(-selectfg)]
    }
}

variable version 0.1
package provide ttk::theme::arc $version


# THATCH /packages/arc/arc/frame-gap-end.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAIAAAABCAYAAAD0In+KAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAASSURBVAiZY7x///7/Hz9+OAIAIFEGxyH4Q+EAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/button-active.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAADDSURBVEiJ7dVNDsFgFIXh97ZVDRFdgrEdNGEkRpaBXdU6DCUMDK3BBsRP2mqLa0CFxPCTGHxndEfnyRldAZgvNh2cWoxqH/AxkwJY3q7uZDTobj0AxJ01A88N2w3EkKLA/nj2kjSPgeEDQnpPxNQaBPywFURJmgvAE8I3teQDE+rV7fyg/2ssZCELWchCFvoHqPqwhYLRVw6gSv6orSCR1f6QemG7EZnCFIrd6bxWKF/Q7eKMk6yMk+xgwnjHSr26U4A7Wuc1O72hp5cAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/entry-border-bg.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAADtSURBVEiJ7da9SgNBFIbh7xwzu9nsGJSEyS2qYCeIYCV4CYHcWZqk0WrHDP4wm83+uMfCQpCUs0Vgvgs4D5zqpXJfSVk1cO8H1G0PEUGIERFSxZhdjpFnCci6Tyl2VZdr9aDV98oY40NA1lpd1nzj993zYj4ZYb0pZPPydhfi+LFtX3f3620hXLc9pmNZDQWdp/2ybnqwiCDUu47NGONFBDwU8H8RilCEIhShk4SICNZaPRTgnJsSEThVDN+eXQ0FfR3oOk34L060Th5z1S2DxknDt77snhbzyYh+c6uF+6hQN4FzK2HMLjLkmcIPc0txATCnSmQAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/button.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAC2SURBVEiJ7dYhDsJQEIThf5umhipC04CBhGCQaJCcBLhVOQxwACQJroo0T9Q0FRUdTENQqCcQb+VmM59YMwZwf7wWJgqhHZDgZzrgKjhu1rMyBhD9ORuPlvkkTczMiyIpqVyzcnVbAPsYwGRbnwiAmZFn6dzV7RQgGvZekW+M4RXR71N/E6AABShAAQrQP0GdJO/hQ2b3gQy7Va4pfWKSqFxTAheAGKBHB1e3xVAkfNatp+AE8AZ4XT+LRTXrnwAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/arrow-down-small-prelight.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAkAAAAGCAYAAAARx7TFAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACaSURBVAiZjY69DsFgGEbPW2pjch3iFkwSo8Gmk8UF2L+Zr9HaRNrGzyC9EIubkIgOFguj7zU0mtg843mSkwP/zsbJLYyzwQ+L0r6NkwLAAxB0q7jjfJl1ARbRpoNoLiq78gdUVcJVugd6qjL0hNyh59fjOjLGuNIkos+WNwEuInpSKGrv5tgY4ypT1WHXbRr1g/p+MJsG9y//AGrNNoujAicqAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/progressbar.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAgAAAAeCAYAAAARgF8NAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACcSURBVCiR7YwhDsJQEAVndzWkvhygEllNuEFvUYHB9ASkvregCWhENWeoqsGSFND9HwMkJL9oRCd5aiZPALKqSxArPX4FgEhjYkWdx61kVZd4sTMQ8U1vaqkiVgYkQOSGYaef2wBOWCvIbCwQmOuYfDMFU/CHgX/88DdFpBmzHk5qYgXQB/xVnG61zuPW1FLg6OH+2h6ny8NmcXkCrhMp9eoEdDgAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/focus-line.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAUAAAAFCAYAAACNbyblAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAAiSURBVAiZYzx39dkaBnSALnju6rM1TBiqGBgYsAoyYjMTAF4MDNvdjO5EAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/arrow-left-prelight.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAYAAAAJCAYAAAARml2dAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAC8SURBVAiZTY4xSsNwHEbf94+kYOmgU+9Q8ASCUrDn0KaDOFThXwS3goOmcWkggVIaqeDSQdykZ/AAHsAjuDU0v04NvvF78PHEP8bjVdg8/pvLuNB+TJK3pgvLD4Me8BwAPOX5USB9AecyxaO76OFgkr22XVmtgY5k1/42mgE4V1bvwImMzA8Hs/2101aXBj8mbpJpcVUL7/u/wdZOEd/CFi/T4h6grorjRSto8InoGjzWAiBN08aGwyWmsx3nYzbQhXRUGQAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/arrow-up.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAkAAAAGCAYAAAARx7TFAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAADCSURBVAiZY2RAAnFxGdL/mFkW/WH4l7Bi/rTHMHEmGCMhoUDgHzPLVgYGBicWBqa9kSn54iiKYmNLuP8w/tnOwMCg85/h/yQGBgYl5r//NicllfEyMDAwMKWlpbH+Z/25hoGBwZyRkSFr6fyp+Yz//ycyMPw3+f3/68aEhAQOZi09y8UMDAyB/xkZqpbMmzKRgYGB4dKF05f0DM2+MjAwpv1nZFNi+s/A4Mz4n6Fj6bwpHcieWDJ/Sg8jA0Prf0ZGOwDHDTxDCfo7IQAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/menubar.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABgAAAAgCAYAAAAIXrg4AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAA0SURBVEiJY3z+4vV/BhoCJloaPmrBqAWjFoxaMGrBqAWjFoxaMGrBqAUjygKWDx8+0dQCALk7Bs1xrPaCAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/slider-vert-prelight.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA0AAAAcCAYAAAC6YTVCAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACMSURBVDiN7ZSxDcJADEWfc5EiNmCHW4mIKUA0QMEoN9bVUUYAIh2mgEghRlwVqvudn/xsV4Z/ReYgxtjchnRB2QAoBCfp6L0fxp56Lr2F3WTqXtUpcBhZZXYrrUVsp7WVYJ1j36RsilSkIi0r9YYI3U9JIRhH9YOZb7Rq3Ol6T8DrhVUQRB7n3MnL5AmCqyQCjLRL5gAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/combo-entry-button-active-rtl.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAB+SURBVDiN7c6xDYMwFADR+8ZBiBRhhAySTJO1YA5KCgpKlkiREheABChOQyR6m+7fAE8nAHXT3zGXEu+fQEpgFgBJqmtmk+KWI4Hg++N2FHnsYPAl/E8hDT08ZiJaiiqqqKKKnoQuHpa4qEg7uKmLBVuA72Ze47yW4+ximPwATgsbpVsJ8AcAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/menu-radio-unchecked.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA0AAAANCAYAAABy6+R8AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAFdSURBVCiRjZLNLgMBGEXPN0aVWGjUXydRQiRiw1oqkXgLb6CLxqOITCy8h60oESxaFm0k/qox06AyI60yOvrZaGJBOet7chf3Ct84K7ipD5G0QAo0DjwKso+qPT+XOGjnBGB3V83YSGUzEulaGbdiTl9P94wIcaD68tq8KLv+ePDe3PHvE5nlZQkBOC26W7eut6eqNf2Z2s2df5QvOjaA5IruUjRibs9ODSWAfn5BVevn149PQRiuGiBrE9aA00kAEJH+CStWoiVpUyAV7TGlk9CmN9o9DUyboHGRfzkAQ4CaIFVVFREZ+8tQ1SpKyxDIvgbh1X9qGm/hJZA1ULXLjj8JvHRuoV6ueEkMtQHIFx275Hi5zjt5x7lCZRPABPDvExlwNxqN5kjSGjjtjZpTIjKoSrXx1ry6db1kELROnh9G1+HrRm3y584iLUmjpBCGUR6ALIbaC7PWYTv3CUs4y687wXLtAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/combo-entry-button-insensitive-rtl.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAB2SURBVDiN7dUxCoNAEEbhN7JsQL1DArlG9KSb03gPxSaW24RgRFiLrJB+p5xX/NN97QjAtMSbg5CgAzyFuTzPpvb3tr54kTJw3fYfmuChAZ5V+aqB/6hqhhpqqKGG6qJbSsqowPD+fGctWADGV7w6CAg9Ci/6ALkSF3kBn8Z4AAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/combo-entry-notebook-rtl.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACUSURBVDiNYzx/7dl/BgoBIyMjAyc7C4O4CA8DHw87pcZBwNWrV9nuP3mXeeXWy98fPn2n2JEo4NHz98U377/+z0hNQ1+8eMH94v3/L0zUNFRCQuLr////GahqKAyMGjpq6Kiho4aOIENfvXrFw8jISF1Df/xly+DkYKGOYVevXmV78PRdDqziY6RaFc3BwiAuDKmiASKROQr3+FAjAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/minus.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAsAAAALCAYAAACprHcmAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACwSURBVBiVlZFBCoJQFEXv/YQoLsRBUNQo2oobaNigZTRo2AZqF9GsRiUGmRvQFaip0H+NzKD62JldOFzu4zGME++huSUwAkB8IgTOVOIjiNJ9VlRiIisqOd+SnSIwcR3rS2GL61hQwqkSwDaazRbAVl3Eht57WK7WCC/XVx4O+ljMZ60QRKnxuIYgSuWvGYpA2UUkUCoRHPN7bRTzooamHBjGiSeaGwHG+PFBACdS+0+yXH6f0kN4sgAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/combo-entry-focus.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH3wwYDSMzdkATDwAAAJpJREFUOMtj/Prt+//zj38yrD//jeHx+78Mf/7+ZyATMMJZR25++J8+/+n/Cw++/v/9599/CgADDDMUL3/2/8KDL/+pAOCGMj3+8JdBW4aLgZqA6c/f/wwszIzUNZSBBmDU0FFDRw0dNXSQG8rCzEhJvYTdUFlBZoarz35Q19BAQy6GaXvfM5x78JVqLmaEVdEbzn9jeESlKhoAvdvQT/IZeXAAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/checkbox-checked-insensitive.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAEPSURBVDiNpZBBTsJAFIa/mbSZhUFYaGNXGlnJzp1nMNFo9BbewEAgegZv0QTxMm51YTS2qUUUUhhnXBgQUihF/928vO+b9x78MwLg9OZhTxh5jqBciLKmayVB+2LnXgIIQ3EYQMiysPIMQI4LK04OUPkVFIhyJfvbKlMvJFCupH60weWhx8HuWr5ga92hpGQGrvmKZKB5jNOZfmf64Vccrk42efu0XN+9MjRM4LinadyGvLzrxYJ0COkIqp5L49gj/TLUfEXU0zTnwJkV4r6m3g55ikdUPXcpPPcGSV/T6kQ8J5p4CZxZYXqSVifEdciFFwoAoo98cJyfFazpFuqeTTIRWEmwoiQR1gn+8Gk238RibVQKoKtdAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/arrow-right.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAYAAAAJCAYAAAARml2dAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAADKSURBVAiZY4xJyH7JyMi458cXkcTVqxt+MUABEyMD47z/DAxR7NxvNsfGlnDDJJgvXTi1V8/A9AcDI2MaA9NfN20zg/VXzp79xghTEZ2YHc/IwDiHgYHh9n9mRjdmmMTlC6cv6hqaijAyMPow/mcwQOhIyE1iZPw/i4GB4dYfhn/uTAwMDAyxibl5jIz/5zAyMlxgZWC0XzF/2mOm2MSclv8M/ycyMDDsZ2Xgcpw/f/JrBgYGBqZ//xkSGRkYlgnyMHrNm9f1GWY0ADn4PSHVIMlRAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/combo-entry-insensitive-rtl.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACASURBVDiN7dU7EsIwDEXRK9uTCd7/CmlSUDDBzBD8QRTBK7A6fBdwChV6ct3uymAi4J1wWQNL8EipdRhVhVwbezqIqxHae5fGI71wViDAEjzto7aoyHkKU7Q30YlOdKJ/hKqeP9UUzbXhnRAsMFXIpbE/D+IaCNstDaN9ouNvor+uKC55YMQO/AAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/menu-arrow.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAUAAAAICAYAAAAx8TU7AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACWSURBVAiZNcwxDsFQHMDh3+vr4jBetUN7GRJMhorEJJ0kFsRGjbXULWwS5C1tnkvYJFbib9HvAJ/uDsYPE8a42l740+0oEQUb00nerrZnAH2v7DUI4xeKlYmSlqvsSQO42t6CMHmCLEwUK695viIfACX4GqA3TEdAjlLr8rDLvG4/nYiwF2ReFtsZgI9iKorsWOTLpvoBupIz9ctER/MAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/combo-entry.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH3wwYDSIWJF/2CQAAAJNJREFUOMvt1TELwjAQhuHvQtUWTIu4KNj//8MEQTC0FuI1CfQc6iI42RMc8i7ZHi7TR/7B4jnCdSNCmiAi+DJ6vevCc8T1xmgPFrWtQERYWCxcN+J0rNHYClqZkCY02xKaGRHR+PI7ih+U0YxmNKN/jhLRkl36jG5WBoMPuuh+V+J8uaMfWO1imic6wfWMEFUmGk/O1j5fvPAAZQAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/progressbar_v.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAB4AAAAICAYAAADuv08kAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACUSURBVCiRvdChDcJgFEXhc9/TJPUwQCWymrBBt6jAYDoBqe8WNAGNqGYGFAZL0hTdPgQS3f8s8CVHAGX7zJE3QexAKxYpPki9y+uuWj9Uts885HcgWwb8a3DzwpA3CVGAbJ6mk/32pm0We0uNAgjCkPrUcMDNXF4DQ0L3rdmO1lXrh5sXwDVgXEoLGAPOzLa9HDavLxSqKcnRL70HAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/arrow-right-insens.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAYAAAAJCAYAAAARml2dAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAADOSURBVAiZY4xNzK5j+M9w68dX+9WrV4f9ZYACJob/DGcYGBlMOLgOJYeGNrDBJJgvXTh928DI9DcjI6MFM+s3dX1d9SuXLl36zQhTEZuUY/L/3/8wBgam1z/ZuGYxwyQunT/1TM/AhJuRkUGL6f9vaSaYRHRCvikDA5PV//9ML7/+Y1nBwsDAwBCXlG/z7/9ff0ZGhqc/Pv+ds2H15C9MsYk57v///wn4z8hwV4Cbafrq1dO+MDAwMDD9/89g8Y+B8YKqnMicyZMn/4QZDQB2wUrq4DzELwAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/down-background.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAMCAYAAABbayygAAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH4AEYEiskJ4yJRAAAAEJJREFUGNPtzDEKgDAQRNGH5Kqe10IQTGcjBFsrMaw3WARbB373GHfvkTUte8Dg5X74GV5QMtGOc0OFMq8te6rBCA/2ri6Xz1tUIwAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/down-background-active.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAMCAYAAABbayygAAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH4AEYEiw75cUSdgAAAEdJREFUGNNjvHzj0X8GPODJi48Mng66jEwMRIJRhdRRyIJL4j8DA8O3H39/sLCwfGVgYGBgefLiI25TWFi+srKw+TEwMDAAALJnERrkRc5GAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/slider-prelight.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA8AAAAPCAYAAAA71pVKAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAFGSURBVCiRndLNSlthEMbx/zOny8RVN0oPkWYlJRH1KroLSPQG/ICA9+A1uCi0XoFK1t3pDSjUVReSiDEIkhSEnO05j4v2iGANmmf1LubHzDCveJb2sZP8frgJ3kEsI6qYieFXiB+NUXq0v6+irFf5aB0M6knCT5t5oMLLZEh3UvG126n1n3DrYFAPcQ6eQ4r/wLJXjj1R4rVup9ZX+9hJMbr9bbsO02DplWP3muN06UN+P9xEzL8JAtgJsHD58XYjkHdf2XFaKpJ2Ami+E/4doPBKIFVnwZIqgT2ZqbOLLGwuZ8FEXEQE34HsnTRT4cNojNIjpDtQ/hZllAsNm3/SEwGsf7v57FwXhKr/7vg6tCcJxerJ3uJ1AHQ7tb4Sr2H3pqyQBVyVEODpV3U7tX5znC4ZtsFnwAMiBx5Ap5itxvjTlxICPAKo/IFf4Wx34AAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/combo-entry-insensitive-notebook.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAABzSURBVDiN7dUxDgIxDETRn7CEAhD3PyWCBGltvDYHoFwjUeQf4BXTTHH3EDX6EN5bQAR7W0SNe1+5nRutLbtBgPockgoCVNsiFQSoGRt+oz9oohOd6ET/HS0lHz0eCqqWi14vJx5DU+Hi7rGK0V+CJV30B/v1NKMMRKCwAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/up-background-hover.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAMCAYAAABbayygAAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH4AEYEigVXX/avQAAAFNJREFUGNNjPH/t2X8G7OAXAwPDof8MDClGWlIPGf7jAP/+/fv/9MXHB+evPdvNwMDAwITDNAZGRkYGSTFeeQYGBju8CmGKGRgY2AgqRAajCvECAJkPK4AZGHK0AAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/entry-border-bg-solid.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAADQSURBVEiJ7dbBioMwEIDhf0I1iou2BApC3//JBKEgXaVZjYKzhyIspcd4WPB/gHxMLjPif0b140z3mAjLiqoSIxHBJgZ3ySjylJMfZ+7dyK2uKAuLiESBVJXBB5q25+qEU/eYuNUV1VcWBdgSkdebNbT3AROWlbKwUZG/lYUlzCtGVaN916dEBFXF7Ca8dUAHdEAHdED/Etr2xV5t+87YxDD4sBs0+IBNDcZdMpq2p39OUSdTVfrnRNP2uHOOvM6the57JMyRz63U4M45RZ7wC6i8XpS7YvAwAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/button-empty.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH3wwXEiMTAjfH3AAAAClJREFUSMdj/Prt+38GOgAmBjqBUYtGLRq1aNSiUYtGLRq1aNSikWkRAB13BBF9wGnqAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/slider-vert-active.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA0AAAAcCAYAAAC6YTVCAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACZSURBVDiNY2CgF2BEF/CcdJudg4mtmfE/YwwDAwMDA9P/xcyvv9SubtD+BVPDgq6Jg4mtmZGBsRRu3H/Gsn8ifP8ZGBgqYGqYMK1mjEUX+8/wPx6Zj6GJgYFBgpAYNk0EwaimUU2jmmip6T/DcyzqnuLXxPR/MYY5/xlRxDBKo+9/f9VxMrMxMECLMEYGxsXMbz/VE3QzTQAAmzMhKWbmP+QAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/checkbox-unchecked-insensitive.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACSSURBVDiN7c4hDsJQEIThfzcvGESx5QJgQHGUx424DelNMIApB4AmGFIFouwimqAIWYLt+Plm4M8IwO5wmWuyrK6TSMmF27OjWi2ndQJQlfViVt6TamjVjMf+dM7ApgfEi6RaRG+rUqr3Y7HJb9gADMAbEGk7syZa6swac2kBEoA51bG+ZsVDgCFjH/n2978f8gKtDit4voId7gAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/notebook-gap-horiz.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAQAAAACCAYAAAB/qH1jAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAAXSURBVAiZY2BgYGD4DwUMDAwMTAxoAADLeAf7sjIgbgAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/up-background-disable-rtl.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAMCAYAAABbayygAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAABJSURBVBiVY2RgYGC4//y9AgsDw5z/DAy2DAwMbAxYAAuUmMvNxabMw8XOxsiITRlU4X8GBht8ihgYGBiYoDReRcgKCYJRhXgBAP0aBz92YsejAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/arrow-down-prelight.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAkAAAAGCAYAAAARx7TFAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACvSURBVAiZXcw/CwFhHMDx7+/xJyW8FYvNxOotUNeVS8pERBaD5M7wDIarO8qbsAh5Ad6A3WATg8F5TFfynT99xdPhFWHd7dgj/nJ1OBGwFbDHMPR0OPgFCx10BcbASeUybwvDFph6etUE8HRQN8gcODzzyhIA191kJf3egSmJYWmENnCOXlT7ffsh8X7m+4XkK3EEKQIXk06Ve63GDUDFaOA4dxWlahj2kXwqMQD4AhbjObuovFCrAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/toolbar-entry-border-bg.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAADrSURBVEiJ7da9SgNBFIbh78yZYV2zrJ03kRtTwU4QwUrwEgK5qzTZ+LMKgpDRWBk20XV+joXYxW62EOa9gPMUp/nIvrxJ7yK6bYQLACBIE8EwUO0rFEZB9y7ivYu+LNQFeZqOx4ddCqZpVhVzOFlv4nU9Io35nZWbB3uW4viubh/t+fzeinIBiD1Ph4LCJ0+cBzBbLFM95c9mi6WooZHfMpShDGUoQ/8UIjTNqhoKaNu2BgjKMGBKORoKgj44Nhqgp+dXWW+iLwu+/NpiknKc6L142ju5qkes6WduCbqPAOeBpHNLA1XJKAzhG9S9Y96nfkAwAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/notebook-entry-border-bg.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAADfSURBVEiJ7dbBasJAFIXhc5PQJHTIpjK+YrsXxQcRfDA3ulAwhWlGA0NInSTG3C5KKWQ9WQhzXuBbnp+GYeCqblBcv2HbHswMFyMipHGE+ewVmUgAU914dyjuZ2UWWmvhRAGgtRa5MsvdobibyjL2xwuflVm4AsbLlVntTxcObNsjCbvtVFAcdhvb9AiYGVLKeipISlkzM4KpgPE85CEPechDTwkREVxe+HhlWWZEhCCNIzSPl/epoFsXfqRJ9B8nuTIr13Hy+WXWf3FCv7nVoihr2MZxbiUR5m8CmYjxA2CBf037Svt3AAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/arrow-up-small-prelight.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAkAAAAGCAYAAAARx7TFAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACVSURBVAiZY2RAApMmzRP9/f//Eub//+IKClJfwsSZYIyG+fM5fv3/v+E/A4PLH0amjX19qzhRFP3//5+R59O/OQwMDAr//zNaMTIwSv5l/ry4oaGBCa6ob9LcVgYGBr9//5i8SwuSTjIyMfowMjC48gjIdiBMYmBMZGRgiigrTLzAwMDAUJSbeJnhP2MYAyNDFAOxAACG+jA01QG00QAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/empty.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAsAAAALCAYAAACprHcmAAAADklEQVQY02NgGAUjCAAAAe8AAZYMGBwAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/down-background-disable-rtl.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAMCAYAAABbayygAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAABJSURBVBiVY2RgYGB49Pz9f0lRXgZ8gAmv7KhCUhX++vef4SlBhYwMDIffffy6F59iRgYGBoZ7z97LszAwzGFgZLBjYGBgw6YQAL+lEtPOka41AAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/arrow-left-insens.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAYAAAAJCAYAAAARml2dAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAADDSURBVAiZY2RAAqGhq5g5uA+GMjAyqDEiBBvYOLjeJDAw/Vdj+M+wjxEiWMjJzvMnmZHhn8J/Jqb9S+ZO3sqSlJTE+/PvnzQGRgbxP38Y1i6fP/k4AwMDA8tPBq5oJqZ/kv///TuyfNH04zCjmb7+Y1nx/z/TSwYGJqvohHxTmATzjQsnfsibGVxg/8uizMz430rfyOTPxfOnH8BdlZuby/7u6/9Epv//VRgYGHczwyROnTr1N9jf68Lbj99FGP4z6AEARqxGt4i+y98AAAAASUVORK5CYII=
# THATCH /packages/arc/arc/combo-entry-focus-rtl.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACcSURBVDiNYwya8ug/A4WAhZmRQVaQmSHQkIvBUJadgZFSAxkYGBhCG66yWZiJJF9/8WdSgjU3C1UMhYFJu14WP3r3t4eJmoYK/P8/49H7vwxUNTTOXeLrn7//qWsoDIwaOmroqKGjho4gQ6fuf8XDwsxIXUP//WPMkBNkpl7FZ2YmlHbzxb/+RBtuFkZqVdHyQswMAYZcDAYy7AwAnOQqEHiw7MEAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/treeview.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAB4AAAAeCAYAAAA7MK6iAAAARElEQVRIx+3XsRUAEBAE0eWpQSTSf0sucQlN0IPAJTMN/HjSmOsooCJJvdWvqPlWVlDAwMDAwMDAwMDAwMCP72S+v8MXvT4JlNhEZUMAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/line-h.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAIAAAACCAYAAABytg0kAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAAVSURBVAiZY2CAAsb79+//Z2BgYAAAF2EDnjps90YAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/frame.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAKCAYAAACNMs+9AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAAvSURBVBiVY7x///5/BiIACwMDA4OCggJeRQ8ePGBgIsY0BgaGEaqQhYEBEk6EAAAc6glU7YlzowAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/arrow-down.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAkAAAAGCAYAAAARx7TFAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAC0SURBVAiZXYw/CwEBHEDf786fZPBNdCmjyTdQJndyl25xNgNZZbApNl3KwAdQFsUXYLTYlVnK/5/pSt76Xk/sWuMsSDibjjr84bhB76O4hoisVWhXvKD9G9hu0FLoCroxUvFHDViJ0ne8wAewvWYVGAi6iXGtC4DjtNIau62BvKJjQRog+4SkimE4uEi0L/t+JvlMbAELOL5NszCfDM8AZhQddru7lc0t1TCsF5/SIhydIvcFUk86FlJuT8AAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/arrow-down-small-insens.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAkAAAAGCAYAAAARx7TFAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACcSURBVAiZjY47CsJQFERnbpJGGwsbrSwUcUd+3hOTQlDjFrIICztBSBEwW9FNuABB0ELzuRZGSOmUhznDAP/G+pvI2vWozkywGlp/EwGAAEChOKtHMw7CLgAYs+yQjlWRCwCwEjlbhBOh9um5xzzL50K5xoddTFKlKumg1z4p5FZmxdYl7w33lZDU+tL3m7XN0mlN388iSdP948c/DmctvWrqzJgAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/notebook-gap-vert.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAIAAAAECAYAAACk7+45AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAAYSURBVAiZY2CAAsb/////Z2BgYGBiQAcAYgEEAMgaNHwAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/down-background-disable.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAMCAYAAABbayygAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAABMSURBVBiV7dEhEoAwDADBa6cfQGL6Oz5dh6qozCBIMxMEBkMEmtPrLk0zJ6gPoa5LyhF69sPv0O8VClAiJMe54zSA0oe8WcVpBhvABUmFGKbDb+UCAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/radio-unchecked-insensitive.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAGKSURBVDiNpZNBTxNBGIafmd3Ypu2hW1sWknri1K7YBI72wh/gAL+zJv4CL3CURGTBmMjFJtTuyqApS0Nmv+GwsjGido3vaTLJ83zvN8nAf0b9ehHH89YSO/YUA6foAShHkjvO6/iHUbS2+KPg+HQ60p7a74ftWRA0mho6AAJXxmQ309m3DRGZbD/vv3skOD6djur12t5gs3sHxeTfJDn/lD65vZXXO1vhCYB+qK09tb8CBugNNrt3nm8P4njeKgVL7Lgftmcr4FLSD9uzJXZcCpRmGASNZgUYgCBoNJVmCOADKHiKoApdhQgdBa4UaIfTVWFAaxxSnH0AB19F8LRmvVIBwThdKIq5irPUZFnVBqnJMg1xKTBiji6T61CEZBVsRZLL5Do0Yo5KwW4ULXIrkw8X89rfJFYk+XiR1nIrk90oWhTlf8rb959feL4+2Oi1v3SDegN058fWV6lZZrPk+5q19tXO1rOTB+bRZ3oTx63ABS9zGGpFFw2Sk3pwpnJ9OBqt36x+pX/IPc6LnyFsuwv4AAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/arrow-down-insens.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAkAAAAGCAYAAAARx7TFAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAADLSURBVAiZY4xNzK77x8h4eum8KdsZ0EBsYo47A8N/c6Z//xnvMP3/7xybmOOErCAmIceBgeG/6z8GxntMv76+XPmfgeEGIwODZ3RCrgUDAwNDfHymMRMjgzcDI+MdVXmRFYwMDAwMoaENbJy8b9L/MTDKMvz7c4yBicWK4d//p4K8jDMmT578k5mBgYHh2rUDfw31tS79+8+qycjIqP2fkeHtry//Zs6fP/U7AwMDAzPMDRcuXPijrmp4jYmdRfoXC/f81YsnfIbJAQBYu0QINLD8IwAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/menu-checkbox-unchecked.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA0AAAANCAYAAABy6+R8AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAABpSURBVCiR7Y27DYMwFADvWW8DyqzARpkh7OLJrMhAk94SAibwL30aXkeTq+90Epb0RPDAwDUnwkRY05Fri91AzjWGNe0KDOrEckHVjQDOIv/yj26JzlJatMiltDdwKMI0fzZvnDw6/fUFWpJHRFBEH9EAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/tab-top.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAwAAAAWCAYAAAD0OH0aAAAABmJLR0QA9QD2APfrBwyPAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH3wwZCBEvMUa+vwAAADhJREFUOMtjvP/kFcO/////MxAJWHi42Bk+ff3BwMvBQlDx5x9/GJiINhoKmBhGNYxqGNUwiDUAAJlvDdFLOsqDAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/slider-insensitive.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA8AAAAPCAYAAAA71pVKAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAGGSURBVCiRlZNRbtpAEIZnZvFuwMYQRU5FSjlE89gDcI2WMySXqHKH5BjhvY+IXCFpqwiJRoLYK7Nr70wfGiNUKSF8T/Own2ZWMz/CDrOZRMNRfsnCX+vAn5jREIkjRT9J4GbwofcdEUPzHpvicbk65wpuKaI06WhtIgVECMwCzgfIS++55uejFoyzrD/fyo/L1Xld8Y+02zZJRyO8grVe1kXp2hF9ybL+nGYzibiC230iAEAca0yTttlUMBURRcNRfvky6ptiQxJrJIXp4sleUB3Ct6Sj9XvEhm5sNIcwIRYZmkgd4oLRCkIII/q3jndNvIUIgQU0EYljloNkZgFC8KQU/XI+7Dd2cD6AInVPKHCdl94fIufWeSC5QRFRvxfrRRqbkzjev67CeskL92c46A0IEcNRC8bronSF9W9+vrBenovSUUvGiBi2nZbL1edNBVNSmHZjo43+77at8xxkTS0Zfzw9vgPYCQYAgIioxZO94KqeBOFRkyql6AEQrs+y3tVuqv4CBt3B5fjCyxAAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/slider-vert.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA0AAAAcCAYAAAC6YTVCAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACQSURBVDiNY2CgF2BEF9i2bRs7MytH8///jDFQJYs/fXhVGxYW9gumhgVdE1RDKULkfxmfgOh/BgaGCpgIE7qm//8YYzHc858hHpmLoYmBkUGCkBimJiLAqKZRTaOaaKvpOboAIwPDUwKaGBeji/z7z4AihlEa/fvzrY6JhYuBgYEBWoT9X/z54+t6vO6lGQAA/WMjIBxktIAAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/menu-radio-unchecked-insensitive.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA0AAAANCAYAAABy6+R8AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAFfSURBVCiRjdJNSwJhFAXgc19nGnHExlLyI9IGggYC0Xb5J4roJ7aN+hGugqLAlCC/kCZJZQwdHUff2yKVIELP8nIe7uYQfuWp+nHIc1mUIJMIOgFDMNdpJkq5XKK+7BEAMLN4rtoXW1vK0UHaGIQ0NQ5ABzByXb/bev8y3Nm0WjhO3hKRJAB4qrxfbhvBvUwimgag4W+8Rtvp9Ifj9qmVuqH7146pB+jKMuORf8AKVt4+Xc+fXwvVn59l0sZgDQAAzdw3+pBcVCTIDGnqmv5CaWqMiGIKEfSNxE/CEmCFGaPFIbJOSClHkGAhwDXX83ubvJlM5l0irgmaiVKzPdgBMF1jvGbHiUJQSeRyifrY98sN2/kE4P0HWrbTGU9mL3kr2Vgt4qFqnweVwEk2Fe2FQuouAF1KjNyJ12vaTtSbynLBSt6tFrHMY8XOQnKRmUwSCLPEkIhrEFTKW8nGsvcNIY2dFVhfA1sAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/down-background-hover.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAMCAYAAABbayygAAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH4AEYEio4KpbkSgAAAD9JREFUGNPtyisKgEAABcBB9qqeV5PCNosLVpvleQI/mJ088mCY1kDnpT9+j0nggHKX2rYvqFDGuV3dAzX0cAIaYTS+7l+CRAAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/up-background-disable.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAMCAYAAABbayygAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAABbSURBVBiVY3z0/P1/BuzgF8N/hkN/GBhSlKQEHzL+/vMHq8L//xkYvnz7+fDL11+35aQEXVlwmMbAyMjAwMPFLv/l2y9JBgYGBiZcCmGKGRgY2AgqRAajCvECAN6yGlwWKcisAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/line-v.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAIAAAACCAYAAABytg0kAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAAVSURBVAiZY7h///5/BgYGBiYGKAAAN+YDnz3aQSwAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/arrow-up-small-insens.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAkAAAAGCAYAAAARx7TFAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACdSURBVAiZY2RAAqGhWTwcXExRH5m/Ld80b95nmDgzjNHQ0MDy6fuPFAZGBiUOBjYlCzODc2fPnv3HwMDAwARVw3j7wZswRoZ/QkyszJP/Mvzj+/aHPfL///+McEVRCdmejEz/tX8zMs5ZNGviI6bfv+cyMv5Xi0nK8YYrYmJgNGX8/X/JinlTnjEwMDAsWTLr+f//fxczMjIaMhALALu5NUOFNfWMAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/button-insensitive.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACwSURBVEiJ7dYhDsJAEIXhf5vNNik1SDAQCLcAyUmAW5XDALfAkCokgu0mXZoMZkNQqBGIHTmZvE+MeQbgdn/MLTQCG8ChMxHhPMB+MR23FsDCcVS5ZV2VzhgdRQTnQ7/yXWyArQUQWGsiAMZAXZUzH+IEoEh7VeQbI72i+HmpOBnKUIYylKEM/RMURfTDU2b8QAYuPvStJiYCz65vEU4AFuAl7HwXm1QkNOvWdYADwBuldTm+DhEVpgAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/arrow-up-small.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAkAAAAGCAYAAAARx7TFAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACSSURBVAiZY2RAAomJuaK///9f8peFOW75nIkvYeJMMEZCQgLHb4Z/GxgYGVyY//7dGBpayImuiPEPA/ccBgZGhX9MjJYMDAyS7Ny/Fzc0NDDBFUUn5rQyMDL4/fv/z3vZ3Mmn/v9n8GFgZHC9/fBNO8IkRoaE/4yM4csWTLvAwMDAsHTBlMuMDAxhjIyMoQzEAgDwaiyd7egJFAAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/combo-entry-insensitive-notebook-rtl.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAB5SURBVDiN7cxBCsIwEEDRP3ZsArbS+99PEHETiC4mCePKEySuzDvAk9s9Ob1EOC/CdgnEoEiptT8FzCopG8cex6XfOL8Lp1EhwLoqtfnYFAD/RQoznelMZ/pPqbuDyNi0lIYuA1OzRsrGvgX08Xz1jyKoCsc1ElflA6HZK9Ru/46dAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/null.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA8AAAAPCAYAAAA71pVKAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAARSURBVCiRY2AYBaNgFAwiAAADkwAB2bIsNwAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/slider-horiz-prelight.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABwAAAANCAYAAAC6hw6qAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACMSURBVDiN7ZGxDcIwEEXf2UgRI4QVvFIQU4BoIAWjeCz3MAIQyVwabIFIeSmQ8qqv+9J/xcHCvyMlpJSax5AvKB3QGu3fFKKXfAohDACr0rxleyNRoRU4qHoFjgCuVsrWWPYxza5k932fCSH/CBXibD7Vul1/uG78+f7MAJ3AxkKkcHUQRV69xd7CJCM55Sb33oT+aQAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/button-hover.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAC1SURBVEiJ7dYhDsJAEIXhf5qmiipCk2IgIRgkGiQnAW5VDgMcAEmCq9pkRU1TU9GHaQgKtQKxIyeT94kxzwAeT7c0UQntgYww0wM3wWm7mdcpgBguxXSyKmd5ZmZBFEmZ8+3aN10FHFIAk+1CIgBmRlnkC990JUAy7oMi3xjjK5Lfp+EmQhGKUIQiFKF/gnpJwcPHzP4DGXZ3vq1DYpJwvq2BK0AKMKCjb7pqLBIh69ZLcAZ4A6ArP4KxoQ/BAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/menu-arrow-prelight.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAUAAAAICAYAAAAx8TU7AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACWSURBVAiZNcwxDsFQHMDh3+vr4jBetUN7GRJMhorEJJ0kFsRGjbXULWwS5C1tnkvYJFbib9HvAJ/uDsYPE8a42l740+0oEQUb00nerrZnAH2v7DUI4xeKlYmSlqvsSQO42t6CMHmCLEwUK695viIfACX4GqA3TEdAjlLr8rDLvG4/nYiwF2ReFtsZgI9iKorsWOTLpvoBupIz9ctER/MAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/menu-radio-checked.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA0AAAANCAYAAABy6+R8AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAEsSURBVCiRjZK9TgJREEbP3CyBxoKAYCFQYaeVnSCRNyDxGVAXxXcxsqLPYPANxIB2NpRqpTTIb2EDgexYKGaXBPV088137m1G8FBw2jlctQUywCrQQ2iiOLXjZGPeE4Di5WOgP42fgxZZggjViNUtXx1sTy2AvwQAVQ4HsxjAkRScdk5cvftN8GJcdi2jlNQTxlYs7HyYjXiQp84Epz6i9zH72bsG26jqjvclOx9mcz1EMCBsJULYe+HFz7IGiHqTdDzoa6TX/DMQNUDfm7y8T3yN545/BnoGoelNKrcjWu0x46nSao9x6sNFqSH7Z29Z19BY3CxDRbPmupxsilD9n4FzU0rdG4CI1S0DF38Jw0HiFL7PaE6h8poRlRKQ5ev2uqo0Ba3UTlIP894nTbxo14qNUiEAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/checkbox-unchecked.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACKSURBVDiN7ZIxCsJQEAVnPzmClQQvIFaewotIjqQ38RQJfI1gGdRIzmD+bpogNoEV20y1zQyvWPgTASjr107EDsDK6TVqFNv18gRAVbf3d9KzOUlJY3VtG4Bs3JFnQXLv7BBk87m90mRsDsyBr8CzV4teqVeNGA8YX1kkFJdbdwRzJmSByP63rRMMkEFPSJxna1YAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/up-background-active.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAMCAYAAABbayygAAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH4AEYEi0z8gWrBQAAAElJREFUGNNj3H7g8n8GHICVheUdCwubr4OF8jEWGQl+XOoYvv34y/X5y4/NDAwMwkwMeAAXBzPH7z9/hBgYGBjwKkQGowqpoxAAFhsQGSllcz4AAAAASUVORK5CYII=
# THATCH /packages/arc/arc/handle-v.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAIAAAAYCAYAAADQ+yzZAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAAaSURBVAiZY2AgBzCev/bsPwMDAwPTgCrGAwDDtgqoV12ImgAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/button-focus.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH4AEXFA010gxGdgAAAOxJREFUSMftlrFqAkEQhr8VOZDYJCiiTQSTxi7pU8ansFDUTsiz2J/gg1jlBTbVBuxsTmSLa+RA3XOsDNFCC7fcH4ZhmOKfr/pHAejfVVMJsSAfQIQf7YBvgeF7u7EsAgiHafXpoVWrlCOllBcXEYnWdvNq0ywGPgHQJtnunZNufywuz731vXOiTbL9c9cmEZfnXutkpk0iAIX/uL3hF740iydnc+Ha8h5dHh2IAlEgCkSBKBDdOvoU5T5jvNsfn0W5Avgxq3nlsfRSq5afPT4nrO1madNs8dZudIoAB2Rg0yy2aVb3/G4tBEYARw7NWnAV55vyAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/combo-entry-focus-notebook.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACcSURBVDiNY/z379//Mw++M6w+85nh4dvfDH/+/megGJy69/V/2oJnvyftfpMZ2nCVjXITGRgYSle++D/zwNtCqhgGBUwP3/1mYPj8cyY1DWUImvKICoGICpiobeCooaOGjho6augQMJSFmZFh5uZnXFQ1VF6YlYGBlz2dmoYynLr39X/qgme/+3e9yaZWxccIq6LXnPnM8IBKVTQAQFlEJAY80JEAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/inline-toolbar.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABgAAAAgCAYAAAAIXrg4AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAA+SURBVEiJY7z7+OV/YX4eBlqAtx+/MDDRxGQkMGrBqAWjFoxaMGrBqAWjFoxaMGrBqAUjxgIWBgZIM5tWAAA3xQm8GGbasAAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/combo-entry-rtl.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACcSURBVDiN7dUxCsJAFITheWuyaxIFJZHkfoLYexDBi1mtVrGwkHUtbKJBFJ+FxAvkde4c4GO6n7a7E6PniAgmVsinCbIkBvUFAcBaq4fjcn5vX5uySCMJ87fD8bLa12cWedrNOZe5KzdKEq2q6sbMEEW7BTSgAQ3oH6He+xERQbQnzXOwNJrlwmey2aJ9vNdlkUYklmitkE++if4AfvctMrA3GeMAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/up-background-rtl.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAMCAYAAABbayygAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAABPSURBVBiV7cqxDUBQGEXhc0VeRSUkOok12JSZlEawhaugULz8FnCa03wC2PZjkFmMZyCRqQQw59o11di3dZKUczeUNUUIoHgeojf87IdhF2rBC2awU46TAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/checkbox-checked.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAEkSURBVDiNpZBPLwNBHEDfjN3uVnrsSmjrgBNxcPUR1EE4+gB7cXBFcOLk5CD1CZyERCI+TUPaNNWm/sWGbHd3HJplmzW0vNtM5r2Z38A/EQCrJ7dlInkKFAb06gLhnm+UriUAkawMIQMUFaoCIOONIeSYUjLwK5YpWJi0U/sDBSxTsFN22F52WJwZ/TmQNQXGiPiSDcHWUp65gsWjF1Jt+/pAzpYcr49zuDZGzpI9uZxnvmjTeQ3Zu2zRfA76AkZyEYYKP1BMOxn2VxzefcXshKWVUy946yp2L1rcvwRM5TM92dPL3/7BgxdydNMhjBSRgoOrtlZOjRBTbftsnjXJmpK7TlcrawMAjSf9rUniEeoDne6n9hkQCHfISC1Swv3DpWk+AHhxYmvEzoBNAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/entry-border-fill.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAUAAAAYCAYAAAAyJzegAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAAXSURBVBiVY/z///9/BjTAhC4wKjjcBAH/ywQson+2hwAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/toolbar-entry-border-disabled-bg.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAC+SURBVEiJ7dZBbsIwEEbhN2NjK4EV3P98RSokm6RpQjPTRRBqJZZmgeR3gPkkb/zLx/nTV3PmxVkNwCmTEBRyEoIKcTVn/oHT8UDbZETKMO7wNc1c+5EUnTgvzul4YN/mMsI9ER43L92ArgZtUxb5W9tkzEDBiz3Xs7bbjr6O+F+FKlShClXoTSHBS82EJ5kZIGjQ7W9/VdP3DVWIOQnXfgQoPk7GaaHrR3ISYlAhRefSDZgNlJxbGiDvhKjCL8qlRLskmyyhAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/tree_header.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAcCAYAAABYvS47AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAAjSURBVDiNY/z///9/BgLgy5cvDEyEFMHAqMJRhaMKRxUSBgC90AcQU6jw+wAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/trough-vertical-active.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA8AAAAiCAYAAACA5IOiAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACLSURBVEiJ7Y6xDcJAEATnzIuEJhBVOEAkUAA92CH9kNgtUADOTOAyED2QAH4dMa/H/KfoJtvVjrRgZCGxcn+8LsW7RtASYUDH+nRY3cJdEZML71pBt8ACZYe4JrqLH9L1Z2STITP/kSflJEw22eT/l59BfiTLilyCqk+WhVcFdMBdlfPMu/rLQyOHN9zVHSw6i3o0AAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/combo-entry-focus-notebook-rtl.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACcSURBVDiNYwya8ug/A4WAhZmRQV6YlSHUhJfBRIGTgZFSAxkYGBhCG66yWVmKJ197/mtSqh0/C1UMhYHp+98W33/9u4eJmoZy//o948Hb3wxUNTTOXeLrn7//qWsoDIwaOmroqKGjho4gQ6fuf8XDwsxIXUOZGZgzFIRZqVfxWVuLp119+qs/zZ6fhZFaVbSiCCtDiAkvg7E8JwMAHKMoYeEMHycAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/slider.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA8AAAAPCAYAAAA71pVKAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAGeSURBVCiRlZNNbhNBEEarqnuYKJ4BlGhIbGEFOZsskKMILM6QHCC5gTkT4QSYA/gQTCJwQIhNEPEQJ/5ZWN2WcKa7itVYswHbb1WLeqpafB9CiU5HVOMgO1Ma28xwyAwxERgi+uxyd/66Wf+AiFzsYzGkVzf7hNTdCIPqThJF8WYIWhPkjsHO5nA3tnb+kN96749bzb3rhZxe3ewjUFqvPX2cbFUI/sFoYn1/MDUs/lWruXdNnY4oQuouEwEAku1IPa8+iZVSXREhahxkZxthUF0mFjzbjlQY6Fra658SKXq7k8TRKmLBbhJHWus2iUgz3ny0jgtRJQQRPiJmiLVe6eMFgSbwDBERgXGOlxslcsegCCwRwRczm68lm9kcAPGCXM7v7sbWriPfj4x17N+DiNDlt+zHcGycrMD92LiLr7+/iwgRIrL3/rg/mJrhxPr/XRxOrM8GU+N8foKIvMj2p96vhlKqGwa6tpvEUVQJIShne2TsnwefOZ+fvDl88ROgVAwAABGhtNc/1Vq3WfioaBUiXjr2562X9Y/lVv0Fhn/loRXxjhoAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/menubar_button.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABkAAAAPCAYAAAARZmTlAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAAwSURBVDiNY7xx68F/BhoDFgYGBgZ1VXmaWXDz9kMGJpqZjgRGLRm1ZNSSUUuGoiUAEE4GsbKIUnAAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/combo-entry-notebook.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACRSURBVDiN7dVBCsIwEEbhf6Qo9Qi5oBRXHsd7mYVdVCk1ENQqpTYNhowLpRfobIS8A3zbRzFG7voR9vaC8wHMjNk9u4EPpX2fmrbQWi/niwCO1ZVr89iJYL8WzgdkcHtRlJmhlBpEUUksoQlNaEL/BCUiGGPWomi+yhCQbyTRaXznS7uVGh99F+1h7z3cKLPoD++KTRq4RZQTAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/trough-scrollbar-vert.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA8AAAAPCAYAAAA71pVKAAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH4AEXEyUvd3wHIwAAABxJREFUKM9j/PPnz38GMgETAwVgVPOo5lHNWAAATacEEeeqeRgAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/arrow-up-prelight.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAkAAAAGCAYAAAARx7TFAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAC8SURBVAiZTY8xa8JQGADvfU0lUAvd3ToLXQSnDIUO/guxmqWDL5Cg4CR0SbAYcEtBHk3XLtKha/9H1y6uuhRM3usk5KbjtlM0WK/fOlaqshY7nE/D33NXZ8lzc1OL/QbugB/P2SCKwj2AAKxW5VUt7gvoKscGuK2UfGbZ9hpAiqK4pHX6ANcH9RRHYw1uBPQufHZLY3w5/nlGwQBYJPrxFSDRk3eFmwH37YM1AjwAaaLHaXMi1pMXB89A8A9RATlRBFm/mAAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/tab-top-hover.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAwAAAAWCAYAAAD0OH0aAAAABmJLR0QA9QD2APfrBwyPAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH3wwZCAwjx5yeiAAAADhJREFUOMtjvP/kFcO/////MxAJWHi42Bk+ff3BICHMR1Dxi7efGJiINhoKmBhGNYxqGNUwiDUAAJ3vDdGt1y42AAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/trough-horizontal-active.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAACIAAAAPCAYAAACBdR0qAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACISURBVEiJ7Y6xDcJAEARnzct1IIqwIyIogB5w6H5ITAsuADIiqALRxsPryK0PHJyRkH7CO+3uQKHwJyh3PJyea6UwCNsCtdNWRNywTzf2m9f0WeUSVQpnYTtHCYAaY4/CkN3MZ6xxFJhUWztbxNBjMRF0ny0i3kfgCkRHg2jGZZVC59hZKPyeL0ZDHgeXoJtSAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/entry-border-active-bg-solid.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAADpSURBVEiJ7dYxbsIwFMbxz3YkomxhhKYcAFUiHIETkGN0hrNA9w7t1p6gjGyYAQ6AI7K6C05Qbb0OLQtidAYk/0cvPz0v77GTqUmWZ3xIg1I7WEfwUSQYslSgyBPkWQeRLM94XZ/wPEkx7MWIBPMCWUfYHRssV/rvYfZW0VYZaqvNwdD8vSJefjsMe7GXKW711I+htAO3jrx9160iwWAdgbcmXBWgAAUoQAG6S+iyL9rq53/f8SwV2FdNa9Du2OAxFeBFnmDxpSFV7XUy6whS1XhZaRTjBOxybn1KA+X53Bp0BaZ5gtFDB78P+rvQ0kx+CwAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/trough-horizontal.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAACIAAAAPCAYAAACBdR0qAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACCSURBVEiJ7ZEhDoNQEAVnERyiqhqJAFXV3qQcCy7SuqqikGhU70BSHgIU+QKxbULyR+7Lvp1kIRI5CBYadv3nbKIWugCp060ReAmqPDsN2zAJbYipEbo6SrB23QzqUBgUMVnhKLCl3C+CtT8Uee8WmdAdeLL81YsReHxF5dgZifyfGcrkG/zVdO9nAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/combo-entry-button-insensitive.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACHSURBVDiN7dUxDoJAEEDRv4agMTaUUmjiXbyJXNRjYLU2lsSwrDAhGQs0sd8tLOYf4LXf3R+dkp6gXGe4nOrKuz6OuimLJFEVQpx8GOR2qKtzmvbJOdht18cQZQ+wyoF+YaDMiv5mqKGGGmron6G67FMAsjxKFfph8igtQNE9XzlcQWlnaADesIosFDvLIRUAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/notebook.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAB4AAAAeCAYAAAA7MK6iAAAABmJLR0QA3QDjAOn6VDSyAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH3wwZCAQbJ0esHgAAAEVJREFUSMft16EVACAMxNCDh8Zg2H8vFKaIGhaAHRDFJAt8nTTmOvpQkaTeaihqvpX1KWBgYGBgYGBgYGBg4Md3Mt/h8AW9kQmvGTFx2gAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/tab-bottom-active.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAB4AAAAeCAYAAAA7MK6iAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAABCSURBVEiJY7z7+OV/JRkxBnqCe09eMTDR1UYkMGrxqMWjFo9aPGrxqMWjFo9aPGrxqMWjFo9aPIQsZmFggHSi6A0ADPIJksRyHZMAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/tab-top-active.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAwAAAAWCAYAAAD0OH0aAAAABmJLR0QA9QD2APfrBwyPAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH3wwZCAoi5sEJmAAAAEVJREFUOMtjvP/kFcO/////MxABmBgZGVl4uNgZPn39wSAhzIdX8Yu3nxh4uNgZmIgyGgr+MzAwMDGQCEY1jGoY1UBPDQDQJw7yq9oJ9wAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/radio-checked.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAFNSURBVDiNrZI9S0JxFIef41UpsqGCIpcLclsb6gu4K0ENORYkSZTRRwnu0OvSFGgmaO1+gr5AIdQQ2NugDoFeT4Mml3u1F+qM5/87z3kO/OGPJd7G0n51JhgM7gIJwOqG9LYjcu202nZpL1YbClixH1IIp0Bk8D5tCKQLO2bOB+gNnw+y8lJUNVXMmvk+oKd9N3yz30SNllXcsp4CAL2bfzgMIOPihLMAgV4n6Y0smqOcrEc5XouyYI74EWjSDYh5A5n4BJNjBlMRg0x80n8EYrkBvy6FjhtQ9QYOK2+8Nh1emg5HlTcfIIBWAYIAKpRFmXcHbu7f2Tx7HG6gUu4bOK22Ddr4hX7d0JDdB5T2YjWBdPft+3kR3cjvzj73AQCFHTOnqqmvTBTqiK5ebpsXnz3ft10+uJsWJ5xFJIHqXDclt3T0ytCQ/bn53+oD39ZyHYoCN24AAAAASUVORK5CYII=
# THATCH /packages/arc/arc/combo-entry-button-hover.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH4AEXFAArna0FWAAAAG9JREFUOMvtzjsOQFAUANEhL1qtUOiVFmA1rFJnAzqFisSv82kkmqexA1eiuLOAk3HqZrK87wIqC3mahD3rcVqJhnnr6mYqAVyEigI/BjJR9Mn7AkVRRRVVVNH/oheAkdLGZe+BFsB0wyp12FooAG7mOWKpJtbgqAAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/trough-scrollbar-horiz.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA8AAAAPCAYAAAA71pVKAAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH4AEXEyU3ZBCfdQAAABxJREFUKM9j/PPnz38GMgETAwVgVPOo5lHNWAAATacEEeeqeRgAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/menu-checkbox-checked-insensitive.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA0AAAANCAYAAABy6+R8AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAENSURBVCiRldCxSsNAHMfx753J0A6mBlvqVEQHnZ1cfYKWig6+ithSBFHo6FsEarv1BXyKDEIRIYaQILWEq3dOxqapVv/b/fl97v+/E637p0Oh5SkCh3VldGIkniU0fwMAQjrC0JYIuRbYG3LxWJE/Bb/KKUluz2o0jzazXg4t3+CUJJ1mjYZrc3JQziZmub2qzU27jlu2CuAlntMdhKgPnUcXx1vs1216rSq723YGniPF5eCV6H1e3Kg/DvEDxU7F4u68TsO1mUSKq2FIvAByaJpqeqMAP1BIYBIpOg9BARTePk0116OAR39GdxiSzPTKH7WWG2+ppj8OV4a/Jxmd/JooViyNxPsHjIWxvE8n/F4uzET7igAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/tab-right-active.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAB4AAAAeCAYAAAA7MK6iAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAA+SURBVEiJ7c2hFQAgCEBB8Ln/hlKkyBKYHMAC5d8Cp2uflAaameWxecioTh9iYmJiYmJiYmJiYuJ/0zxa4gu3ew05boLWWQAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/slider-vert-insens.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA0AAAAcCAYAAAC6YTVCAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACOSURBVDiN7dQxCoNAEAXQPyHEdkGEHC7BUxiskiJVco0cyzoKjiPe4FstGFe0kjT7u/nsY6Za4G+pKiaq9m7V6latVu1eJE/TN8c5cq5/Eij8TMhN1Qig9N1hjghcg/Ui+XQMEIDzVreENhNRRBHti5qF7ruKBPwEhL9d8BsNQ3p3zkDIxYMsSx/rB++VEXQiLMNb4JDyAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/labelframe.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA8AAAATCAIAAADAoMD9AAAACXBIWXMAAA7EAAAOxAGVKw4bAAAAB3RJTUUH3wwYCx4B0PJ2gwAAABl0RVh0Q29tbWVudABDcmVhdGVkIHdpdGggR0lNUFeBDhcAAAAzSURBVCjPY3z37v3Hjx8YiAD8/AIsHz9+EBOXIEb1q5cvmBhIAaOqR1UPLdUskGROpGoAvNgOgrFOrBMAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/arrow-down-small.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAkAAAAGCAYAAAARx7TFAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACaSURBVAiZjY2hDcJQFEXP+6UbMAACS8IKKIICDILSpG1QtOzwN+gKP0HRroBHMAQomKABBP9hCgmOK++5Jxf+TZxtr1FWTH66tBjHaX4GMABe1YnqfplshgBRUgwUKo9UANKKskryHSIjb2RuvNYop36vu7DWetOOtEOzBr0Yr0fg9mzC2Frrv3cAzrlHiJmhHF5BMK3r8v5hb+bxNBHAhiApAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/radio-unchecked.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAF3SURBVDiNpZLNTsJQEIXPVOuCBSGIaHCjiWLABYnxLWSnPoSJPE03voQrce8TIE0olR9jTLQ1rSUEGxbinXGhNIJWm3iW58757sncC/xTNG+Y5lNe6Vwj4ABA8dPuCnC5MNGMSmXNi6VdW+5x03Z8fxBeKeaWiIQiEirmlj8Ir0zbeb623OPYcLvvPTBzR2LEzJ1233toWO7Rt9pN2/F/C3+FNG3HN82nPABoAKB0rq2vpi0iKv5QbnZpRMX11bSldK5FAAKq2Uwq91d4qmwmlSOgCgCLn94Wgb69SGwL0AYAiRoAYKIPIxHgY1a+NrhlliVNo90kAGa5BzCJGhBQD4bjIGmDYDgOCLiIAKyT4XijMrN0/7xdpON4ozLrZMwcNGzn0Op5j0rF/wXFfGP1vMeG7RxOczQP0YCzQj7dXs6kskS0CQAichcMxwPXeykpyMleqXD+IwAAGj13RXvlUyaqErANgAToaiL1t0Uy9ncKz0l3lUjvL1IL6AlAVo4AAAAASUVORK5CYII=
# THATCH /packages/arc/arc/up-background.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAMCAYAAABbayygAAAABmJLR0QA/wD/AP+gvaeTAAAACXBIWXMAAA3XAAAN1wFCKJt4AAAAB3RJTUUH4AEYEiobiPGVOAAAAElJREFUGNNjPH/t2X8G7OAXAwPDof8MDClGWlIPGf78/fsfF3764uOD89ee7WZgYGBgYsADxEV55BkYGOwIKoQCNmIVMowqJAgAO/QrSJqIlioAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/combo-entry-button-rtl.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAB6SURBVDiN7dWhDoJwFIXx7zhH0cR0s+HmawhPik9j14bZ7T9gs5oIXgKy0bnxfuW0Xz0CeL66s4zasBLIWNkWwPjdjvnucjrsM0mrwJTShMp09QDnNv91A5eoa4EGGmiggfqig5n5okL3/vN9e8ECeDRtIaiBCoeLHgEgAR0LrFt7AQAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/slider-horiz.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABwAAAANCAYAAAC6hw6qAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACWSURBVDiN7ZG9DgFBFIW/u1aIQjSK9WBTrXgKokHhUeYd5pFIaPwkCmGuxh0F5Wwh2a86yUnOVxxo+XfEQgih1+n2t6pSA1Wm/T2Iv5wOK+fcHaC05i2bZxIZFehiOBorsAQorNEo08yyD8rMYhIiaFM+EZ7fQsQ3JYxK2k4fxsdtXZQDgBp0kkclO1B/PR83efZafvACyK4mFRjpBeIAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/entry-border-disabled-bg.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACrSURBVEiJ7dYxDoMwDEDR72AgDPT+54QWAiS4A0VqpY6hUqX8A+QpXmx5TLOtMTGHSNoNM7IkApUTOq80WqFrTExz5NZ72loRyQOZwbJFhjFABzqHA/GN5hFeiXC82XvGe8Cl3WjrvMh7ba2k3XBmZBvXt0SOMbrriM8KVKACFahAfwmd++Kqzn3nKicsW7wMWrZI5QTXeWUYA2GNWX9mBmE5jpPOK/Krc+sJslRVvTJ8SU0AAAAASUVORK5CYII=
# THATCH /packages/arc/arc/frame-gap-start.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAIAAAABCAYAAAD0In+KAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAARSURBVAiZY7x+/boDBwfHfgAT/AOe+ett8wAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/arrow-right-prelight.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAYAAAAJCAYAAAARml2dAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAC3SURBVAiZPc29agJRGIThd06RFGLhFYlNAl6ApSGKpttGYVuxsTgKOSllV4hV+pSC5ALSpLYUbCI2Ioh/n4XuTvsMMxqGdGVittsUW71e7cA9DviUUS+Wtt/eTwsZCMB/JLFMA+CX46na7b6tlTWGIXkBJQaLiy5POQCM3tNgIsKY5+DD5FXY2GDhTnp2t49JJCwB/T1K5U6nsXQ+pH2ZBYyf894qUdT4B3CCNvD14HbVOG5us+krKbhCPeA9TPAAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/menu-radio-checked-insensitive.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA0AAAANCAYAAABy6+R8AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAE4SURBVCiRhZK9TgJREIW/Gf4KqChAYwxuLOjQUqGlNcFC3mFNfAkfQUN4B4gJ0Z4OqC1tVqINYkIFBcLesUB0KcCvm3PPmZnkjhChdvd2rGplAc9E02JuhmoArv9wXQjWPgG4arVi4Wf5EnNnbEFMBpofdNr1eqgA/wUATOzcfZzXAGS1Ev6uQJSYJRtxVS2D+xVzmTh+NUsxl+BltKDZnTCeLn/fHfOKCqEX7eRXs5QOUqQSSukwhV/Nbq6JeGpCOioWcwl21SKSVjFmUfFltGBXbRbOdPUPfzS7E57f58wXjuf3OY3uZDOkBHENE71Qvk7X4ni65PZxzDaWjr62b/ZexWSw1RWd4lz/6eboVQE0P+iYSP+/wMmk0IGfM1pzcT/0kkjFEA+1DM6mprHANN7r+PvDte8b3BJ+KWoY3pgAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/entry-border-active-bg.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAELSURBVEiJY/z67fv/849/Mqw//43h8fu/DH/+/megBmBhZmSQFWRmCDTkYjCUZWdgPHLzw/+FR7/+MVZkqxRi+D8jzFHsCzUsWrX/Fc/bv/+zzj7605pgzc3CULz82f+pe1+WUMNwbGDK3lflJSue/Wd6/OEvgygT4wxaWSTGxDD10fu/DEx//v5noFZwYQNhjmJf/vz9z8BEKwvQwahFoxaNWjRq0ahFQ9IiFmZGhlX7X/HQyoIlJ97ysTAzMjDJCjIzvGNgzKCVRZ++/8+UE2SGNE4WHP36x0iRvUaE4d9UajZO3v1nyD3z4HdTog03CyOsubXh/DeGR1RubskLMTMEGHIxGMiwMwAAlXRtdigZGmwAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/notebook-entry-border-disabled-bg.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACwSURBVEiJ7dY9bgMhFEXh8xgGLBmS/S8xUgprsKXhZ3gpkiJVKigicTbwFbe50nvXXBrpmamXgipDEmHfhBg83llsLo1HOnkLHrdvY5CfSr14HCfv8YZ8fCYNdzcc+Y09XwXTLp2GALh9o12KGbbJX6li5ivfLWhBC1rQgv4nJDIVUFUQweybUOo1DaqtYzfBxOA5Up6Cldo5UiYGj/Te9cyN9Mq0wXfLWiHePTdn+QJLsVK06uuyhQAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/trough-vertical.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA8AAAAiCAYAAACA5IOiAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACFSURBVEiJ7c4hDsJQEIThfxEYboBCI1EVDYbehB6rXIS6VlQi0VW9QE1J6OBfHvTVkh23k/mSBc+qWKx8PIeDiUooAzpBeTru+3C3iWEx34QuwA4oDKrYLopNlgfVORkD24X7J06KY8eO/x+/gntKxoa1QdUk4xldgRoYgftblF8+9KzJB4jAHCGFi02hAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/combo-entry-insensitive.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAB9SURBVDiN7dUxEsIwEEPRv/Zikgbuf0zIEBtjZymgSZ1tMmMd4I1USV5rtto6uTT6ZphxOFpbZ82N+20maUTEAc3lB14v8bj2T+ibkdQPBAhmuEzeob7cQAc60IGeAhXB5Zd2aAxCbd0XnSflsRTen+7WWJNGmOC5ZLeL/gK68jHnPaNT/gAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/menu-checkbox-checked.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA0AAAANCAYAAABy6+R8AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAD8SURBVCiRldC/SsNQFMfx77m5lSqmFKmpf9LVRURwdxJcurSdfIMsPkGnasHZQUp9CVHE2edwkzaDNEWHDEL/5DpIgtXQmLOdy/mc8+NKq/daJ1K3wC7Z5QviKSLV/ycAcA2mrwA3a1Jb8rOtqSxQsS2uz7Y43ltL3pYix9Z0mw7bZc3p/jryGx24Rc5PNlhdUcmFTmMTx9a8vE24ehpj4rgxah7ZHNaK7JQL9J7fadcrVEvfoPsY8DmJkgTSuhmYePNlw6Fa0kznhoIlqWAh3jic07kPEhCEs1Tw5yNG4YyLhwD/Y0r7bpQKFuLlKQX4Oc1QCeLlgMPIiPcF/M5WCMcI73wAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/radio-checked-insensitive.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABAAAAAQCAYAAAAf8/9hAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAFnSURBVDiNpZO7SkNBEEDPjPGFRiTapBDBymihYqniH4gWsRHERhAFsfM/hIggNtpFguAfCLEWBdMLAQtjCq+PRMOOxcWruTchAadZ2Jk9c1hm4J8h4Yulk6d413tl3sRSBsN+kSs56SjEeMmf70y+NgUsZ4rTai4NdDfu56rmXPZid+w2AljOFKc7sDUzi1jVdRQxhLPc9sgdgP5oq7l0q8cAZibObDWdue8PAJ0fbwvNtRtYGD3OxecCgImmwkWzo70cbyQ5Xk8yMxplO2UiAGAMhQu2FgdJ9MVIxGNsLSYaiQz9AsDa1f9V8A8fIJTD+cOrMmWvRsmrcXQVSYPyDBADUCcFJ5b8m795qLJ5+thUQB2FwODz/S0PVNu1N6Gi6l0HgMv9cc+cZkWk5V+IiOmXZH9Gum5wVg6KU6K1VdCGM2FCRb8km9vzpzACAEhn7vtrDMyDpcT8ZTKjpFBQ9a7Dy/Tv+AYxbYOPLWlj3QAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/toolbar-entry-border-active-bg.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAEESURBVEiJ7daxSsNQFMbx79xzs0XjJErs6FIURZ9Cxw7iI1hFUBBEcBLcVRroA+iQPkAE38EKFrq4lcSUOrVk8ybHqZs43QzC/T/A+Q1n+Sgff8kgL5EMDbKpoKwENmJFCAPCflNjc5WhB3mJ+NWY7QZfrXvcPTlYLmxAUW/iG//7OO6bW+xA4+wxlfsku7Bx/Lfukuzy/CkVlc0EuvC6dUFe4UXpVIBWZ2TnKX/U6oxE1Y3Mc5CDHOQgB/1LiBUh6k38uoCH5GORFUGFAaEKyqO6ICi/vRYQ6OVtLHHfmK2Qr3nGkdVxsmBO3z+rm8NdrWk+t56HBqnludVYIuw1NTZWGD85qWWi/odLzwAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/slider-horiz-active.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABwAAAANCAYAAAC6hw6qAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACeSURBVDiN7ZE7CsJQEEXPfU9ibKxs4hZciXuIuArFxg9kB24hpUuy10JsRBACcaySKGlfCiGnuszAPQMDPf+OqjA/noexizKZUkQSpN244iz3t+f2dJgVAINqF7soE1o1JwRAJJjW78nYgA2Aa3ZaBFT9YNiyyu572pUQKNtCZ3lXNjPV3fUPX2WxG/kITCkwDeS6COX+/tgH6utp8wEgsiQf4wAkHwAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/plus.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAsAAAALCAYAAACprHcmAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACjSURBVBiVYzx/9VkVAyNDHQMDAzsDbvCTgZGhkeH8tWdfvnz7+R8f+PLt5//z1559ZmJgYODm5mTDYygDA1SehwmbZM+EGVg1YVV88dJVrIpZ0E2EKYxNymXQ19NmKCnIQCg4f+0ZhodiEnMwxM5fe/YfqzMM9LSxOgOrydgAzOSvX7//wm4SFHz99ouBgYHhCwsDI0Pr7Qdv6xkIxCAjw/8WAIeunduiBwsWAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/menu-checkbox-unchecked-insensitive.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA0AAAANCAYAAABy6+R8AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAABzSURBVCiR7cshFoJQEEDRN3OGggvQHZgIupK/U7aCQYNmwMw5EDwwY6f8n0y+/K7cHsN1g6RBTSYXFq2itQ1Scz5OpppF6+rT/flOpkFdAgDM9ASClsz7/uj3yIXF3ceS2d0HiFm6V3/hQwI55FnMUUX7BaCrKBAyZXejAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/arrow-up-insens.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAkAAAAGCAYAAAARx7TFAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAADHSURBVAiZTY+9CwFxHIc/3+/pLu8lg02SyUsuJRmNFqV+g02S7Qb/gdV+FosrZFBWA0kxKm70F5goE7m6n0HiGZ+e5SH8IUQnrAbVxsvjn82H/fvXK7+g69X86DAQZ+mkE3rGPh+PLwDgT9BTvUGnDeaYlO6eQJGQ62sZhqEBgCKEULSAp0mQSVfSYmoN1nqucCPm8tNBvF6rnhS9WGkwuVmAlhPL3AGAbR8u2XzRIcjS9f6IMgEpSGzGI3PzPzGxzC1AKyIk3jfvO+0+41ToAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/menuitem.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAA8AAAAZCAYAAADuWXTMAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAAtSURBVDiNY3z9+vV/BjIBCxcXF7l6GZjI1jmqeVTzqOZRzSNZM8u3b9/I1gwASuAG9tKB0h8AAAAASUVORK5CYII=
# THATCH /packages/arc/arc/tab-left-active.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAB4AAAAeCAYAAAA7MK6iAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAABCSURBVEiJ7c0xEcAgEADBg0EDFRX+LUEDTTCReEjxNLcGNo31vFxQAHqr4XEOH42NjY2NjY2NjY2NjX8rAHOf8PgDVukG6A5e8/EAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/trough-progressbar.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAgCAYAAAArBentAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAClSURBVDiN7c8xDoJQDMbxP3XWsOMB3vYcmYk3cuEExrO4ODswu3iBtxs3E8SRQB18EEIQiTNNmjRffmlamFhBM1zd3SwqDkDio0xEU2si10KPLkDYW5SLaGxN5ATAb+ojgLCqgz2A+CAZQM1t2y5cjvyx6sKfNcMZzvA/+Boxzy7Mvjs9t1BEUyAfUA8pdddCayInojFwAopP61HKemPt+jb1DwDegS8pctbf5z0AAAAASUVORK5CYII=
# THATCH /packages/arc/arc/handle-h.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABgAAAACCAYAAABCOhwFAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAAdSURBVAiZY2DAAc5fe/b//LVn/8kRQwZMuCSoBQAR8hU/W80/qwAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/toolbar.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABgAAAAgCAYAAAAIXrg4AAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAA0SURBVEiJY/z67ft/BhoCJloaPmrBqAWjFoxaMGrBqAWjFoxaMGrBqAUjygKWF28/0dQCAJnuBupJkASmAAAAAElFTkSuQmCC
# THATCH /packages/arc/arc/notebook-entry-border-active-bg.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABoAAAAYCAYAAADkgu3FAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAAEKSURBVEiJ7dZNSsNAGMbxZz5CLfQLot2mOYOpW+kdtEcoVXDnB4IrwSMUiu3SjdE7lGZVJWco6a4UUkhbrZLJjCs30uVkIcz/AO8P3tVDpJQqjLZ4CdeYxSlEpqAjzggc28KpV4bXKIKH0RbDIBFHbuG2eUD77VZ9owPyR4vSivDzQZA8AOC4ep6r4Ti+1HF8V4/j5c21P1d0tkxRkVk/L6gmRS+KU1CRKeh6167arfpGZAo0L+BvBjKQgQxkoH8JcUbgjxalvICnSVzhjIA6toUVZd28oM9vctawLZD36YcaBIlount3NSl6WscJ4xdv06/7znGVk9+59RquEWmeW+6+hROvjEOniB8JQGwqg+PXvgAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/slider-horiz-insens.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABwAAAANCAYAAAC6hw6qAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACKSURBVDiN7Y0xCsJAFAXnB8F2IZuAni3iKQQbtbDSa+yx0msRIqkFeVarhrS7hZCpHq+YgZl/x+JoWy2de5wFDbBK5L8bCt6XBzN7joJd118Fu0ShMdKlrv0eoPh8sMkSAzDbxln83MoWhNckaChky+nrXsQxDOXRuR5hDbBOlLohhaoqT4l8M1PeProjQa47sXQAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/combo-entry-button.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACMSURBVDiN7dUhCgJRFIXh/8njFTUYRBBByxTjLMDmTnRXrsYN2AyTHBBheGHKYJhyJohgnxsM91/Ax2kn3O4vMb4euApO5X5dx91mwXyaRomSUpO7IrfvC3CcGKwkhMBqOdsCBwAT9AsDyRT9zVFHHXXU0T9DJcHnAIlWYJO7GqgA4uPZWrg9UAnOAAMmZSRF5AbYtAAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/trough-progressbar_v.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAACAAAAAKCAYAAADVTVykAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACeSURBVDiNxc8hDsIwFIfxbw9NMl8OUFfk9MKNMDvBwlkwaMQ0hgvUExzJMuSyPUxZFhSm7V+91Py+QuYV3+Pun3YzcQJqYBvJewOdiDbOGr8EBPwGlJHg3/UiWjlrvACEn6fCAcppLloACQ91QhyAAg7rgBzTdUCXwb8uASLaAH1C/SWjHpcAZ40X0Qq4AENEeAA9yzjvnds9Ijr/7wOKsSlGqn43YwAAAABJRU5ErkJggg==
# THATCH /packages/arc/arc/combo-entry-button-active.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAABUAAAAYCAYAAAAVibZIAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAACQSURBVDiN7dUxCsJAFEXROyYEBNFWQbCycRuSKttIduU+bMUt2KULWNgmYwj5EL+FIPYzhcV/Czi87rrz5aaET4Dra0rK4nhoUoDtehUkKmSdH/a+lxOQpxFe4oDlYr7zvWwAZjFQAOcAyKKivzPUUEMNNfTPUP3kUwCiNEqB9jk2CvUXvT/aUFcUap2SCuANf/kmDWkJ8UcAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/arrow-left.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAYAAAAJCAYAAAARml2dAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAADGSURBVAiZY2RAAqGhDWwcPG/m/2dgcGaECcbGlnD/Z/6xjoGRwY3xP0MHIwMDA0NUVKYgEzvTFgYGRisGRsbOJfMmV7AkJGRJ/GFg3snA8F+bkZEhffG8ybMYGBgYmP4wMi1lYPyv95/h/9TF86bMghnN9IfhXwIDA8N1RgbG7OiE3CSYBPOVC6c/qRtbL2f+/8+ekZEhS9/Q7PulC6eOwl2VlFTG++v/tw0MDAxOjAwMrXAJBgYGhtzcXPYPX/7P+8/IaAcAkTU6i+UHfMsAAAAASUVORK5CYII=
# THATCH /packages/arc/arc/down-background-rtl.png transforms base64
iVBORw0KGgoAAAANSUhEUgAAAAoAAAAMCAYAAABbayygAAAABHNCSVQICAgIfAhkiAAAAAlwSFlzAAAN1wAADdcBQiibeAAAABl0RVh0U29mdHdhcmUAd3d3Lmlua3NjYXBlLm9yZ5vuPBoAAABDSURBVBiV7cqxEUBAEADAPYE2dKJS3cjJPpe8GalMchowXgE2XrCWmi2dj/74KV6Z2Y4h5v04t7ccsJQ6BBNG9E/xBkZFMmj3JeJjAAAAAElFTkSuQmCC
# THATCH /packages/arc/LICENSE 
                    GNU GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Copyright (C) 2007 Free Software Foundation, Inc. <http://fsf.org/>
 Everyone is permitted to copy and distribute verbatim copies
 of this license document, but changing it is not allowed.

                            Preamble

  The GNU General Public License is a free, copyleft license for
software and other kinds of works.

  The licenses for most software and other practical works are designed
to take away your freedom to share and change the works.  By contrast,
the GNU General Public License is intended to guarantee your freedom to
share and change all versions of a program--to make sure it remains free
software for all its users.  We, the Free Software Foundation, use the
GNU General Public License for most of our software; it applies also to
any other work released this way by its authors.  You can apply it to
your programs, too.

  When we speak of free software, we are referring to freedom, not
price.  Our General Public Licenses are designed to make sure that you
have the freedom to distribute copies of free software (and charge for
them if you wish), that you receive source code or can get it if you
want it, that you can change the software or use pieces of it in new
free programs, and that you know you can do these things.

  To protect your rights, we need to prevent others from denying you
these rights or asking you to surrender the rights.  Therefore, you have
certain responsibilities if you distribute copies of the software, or if
you modify it: responsibilities to respect the freedom of others.

  For example, if you distribute copies of such a program, whether
gratis or for a fee, you must pass on to the recipients the same
freedoms that you received.  You must make sure that they, too, receive
or can get the source code.  And you must show them these terms so they
know their rights.

  Developers that use the GNU GPL protect your rights with two steps:
(1) assert copyright on the software, and (2) offer you this License
giving you legal permission to copy, distribute and/or modify it.

  For the developers' and authors' protection, the GPL clearly explains
that there is no warranty for this free software.  For both users' and
authors' sake, the GPL requires that modified versions be marked as
changed, so that their problems will not be attributed erroneously to
authors of previous versions.

  Some devices are designed to deny users access to install or run
modified versions of the software inside them, although the manufacturer
can do so.  This is fundamentally incompatible with the aim of
protecting users' freedom to change the software.  The systematic
pattern of such abuse occurs in the area of products for individuals to
use, which is precisely where it is most unacceptable.  Therefore, we
have designed this version of the GPL to prohibit the practice for those
products.  If such problems arise substantially in other domains, we
stand ready to extend this provision to those domains in future versions
of the GPL, as needed to protect the freedom of users.

  Finally, every program is threatened constantly by software patents.
States should not allow patents to restrict development and use of
software on general-purpose computers, but in those that do, we wish to
avoid the special danger that patents applied to a free program could
make it effectively proprietary.  To prevent this, the GPL assures that
patents cannot be used to render the program non-free.

  The precise terms and conditions for copying, distribution and
modification follow.

                       TERMS AND CONDITIONS

  0. Definitions.

  "This License" refers to version 3 of the GNU General Public License.

  "Copyright" also means copyright-like laws that apply to other kinds of
works, such as semiconductor masks.

  "The Program" refers to any copyrightable work licensed under this
License.  Each licensee is addressed as "you".  "Licensees" and
"recipients" may be individuals or organizations.

  To "modify" a work means to copy from or adapt all or part of the work
in a fashion requiring copyright permission, other than the making of an
exact copy.  The resulting work is called a "modified version" of the
earlier work or a work "based on" the earlier work.

  A "covered work" means either the unmodified Program or a work based
on the Program.

  To "propagate" a work means to do anything with it that, without
permission, would make you directly or secondarily liable for
infringement under applicable copyright law, except executing it on a
computer or modifying a private copy.  Propagation includes copying,
distribution (with or without modification), making available to the
public, and in some countries other activities as well.

  To "convey" a work means any kind of propagation that enables other
parties to make or receive copies.  Mere interaction with a user through
a computer network, with no transfer of a copy, is not conveying.

  An interactive user interface displays "Appropriate Legal Notices"
to the extent that it includes a convenient and prominently visible
feature that (1) displays an appropriate copyright notice, and (2)
tells the user that there is no warranty for the work (except to the
extent that warranties are provided), that licensees may convey the
work under this License, and how to view a copy of this License.  If
the interface presents a list of user commands or options, such as a
menu, a prominent item in the list meets this criterion.

  1. Source Code.

  The "source code" for a work means the preferred form of the work
for making modifications to it.  "Object code" means any non-source
form of a work.

  A "Standard Interface" means an interface that either is an official
standard defined by a recognized standards body, or, in the case of
interfaces specified for a particular programming language, one that
is widely used among developers working in that language.

  The "System Libraries" of an executable work include anything, other
than the work as a whole, that (a) is included in the normal form of
packaging a Major Component, but which is not part of that Major
Component, and (b) serves only to enable use of the work with that
Major Component, or to implement a Standard Interface for which an
implementation is available to the public in source code form.  A
"Major Component", in this context, means a major essential component
(kernel, window system, and so on) of the specific operating system
(if any) on which the executable work runs, or a compiler used to
produce the work, or an object code interpreter used to run it.

  The "Corresponding Source" for a work in object code form means all
the source code needed to generate, install, and (for an executable
work) run the object code and to modify the work, including scripts to
control those activities.  However, it does not include the work's
System Libraries, or general-purpose tools or generally available free
programs which are used unmodified in performing those activities but
which are not part of the work.  For example, Corresponding Source
includes interface definition files associated with source files for
the work, and the source code for shared libraries and dynamically
linked subprograms that the work is specifically designed to require,
such as by intimate data communication or control flow between those
subprograms and other parts of the work.

  The Corresponding Source need not include anything that users
can regenerate automatically from other parts of the Corresponding
Source.

  The Corresponding Source for a work in source code form is that
same work.

  2. Basic Permissions.

  All rights granted under this License are granted for the term of
copyright on the Program, and are irrevocable provided the stated
conditions are met.  This License explicitly affirms your unlimited
permission to run the unmodified Program.  The output from running a
covered work is covered by this License only if the output, given its
content, constitutes a covered work.  This License acknowledges your
rights of fair use or other equivalent, as provided by copyright law.

  You may make, run and propagate covered works that you do not
convey, without conditions so long as your license otherwise remains
in force.  You may convey covered works to others for the sole purpose
of having them make modifications exclusively for you, or provide you
with facilities for running those works, provided that you comply with
the terms of this License in conveying all material for which you do
not control copyright.  Those thus making or running the covered works
for you must do so exclusively on your behalf, under your direction
and control, on terms that prohibit them from making any copies of
your copyrighted material outside their relationship with you.

  Conveying under any other circumstances is permitted solely under
the conditions stated below.  Sublicensing is not allowed; section 10
makes it unnecessary.

  3. Protecting Users' Legal Rights From Anti-Circumvention Law.

  No covered work shall be deemed part of an effective technological
measure under any applicable law fulfilling obligations under article
11 of the WIPO copyright treaty adopted on 20 December 1996, or
similar laws prohibiting or restricting circumvention of such
measures.

  When you convey a covered work, you waive any legal power to forbid
circumvention of technological measures to the extent such circumvention
is effected by exercising rights under this License with respect to
the covered work, and you disclaim any intention to limit operation or
modification of the work as a means of enforcing, against the work's
users, your or third parties' legal rights to forbid circumvention of
technological measures.

  4. Conveying Verbatim Copies.

  You may convey verbatim copies of the Program's source code as you
receive it, in any medium, provided that you conspicuously and
appropriately publish on each copy an appropriate copyright notice;
keep intact all notices stating that this License and any
non-permissive terms added in accord with section 7 apply to the code;
keep intact all notices of the absence of any warranty; and give all
recipients a copy of this License along with the Program.

  You may charge any price or no price for each copy that you convey,
and you may offer support or warranty protection for a fee.

  5. Conveying Modified Source Versions.

  You may convey a work based on the Program, or the modifications to
produce it from the Program, in the form of source code under the
terms of section 4, provided that you also meet all of these conditions:

    a) The work must carry prominent notices stating that you modified
    it, and giving a relevant date.

    b) The work must carry prominent notices stating that it is
    released under this License and any conditions added under section
    7.  This requirement modifies the requirement in section 4 to
    "keep intact all notices".

    c) You must license the entire work, as a whole, under this
    License to anyone who comes into possession of a copy.  This
    License will therefore apply, along with any applicable section 7
    additional terms, to the whole of the work, and all its parts,
    regardless of how they are packaged.  This License gives no
    permission to license the work in any other way, but it does not
    invalidate such permission if you have separately received it.

    d) If the work has interactive user interfaces, each must display
    Appropriate Legal Notices; however, if the Program has interactive
    interfaces that do not display Appropriate Legal Notices, your
    work need not make them do so.

  A compilation of a covered work with other separate and independent
works, which are not by their nature extensions of the covered work,
and which are not combined with it such as to form a larger program,
in or on a volume of a storage or distribution medium, is called an
"aggregate" if the compilation and its resulting copyright are not
used to limit the access or legal rights of the compilation's users
beyond what the individual works permit.  Inclusion of a covered work
in an aggregate does not cause this License to apply to the other
parts of the aggregate.

  6. Conveying Non-Source Forms.

  You may convey a covered work in object code form under the terms
of sections 4 and 5, provided that you also convey the
machine-readable Corresponding Source under the terms of this License,
in one of these ways:

    a) Convey the object code in, or embodied in, a physical product
    (including a physical distribution medium), accompanied by the
    Corresponding Source fixed on a durable physical medium
    customarily used for software interchange.

    b) Convey the object code in, or embodied in, a physical product
    (including a physical distribution medium), accompanied by a
    written offer, valid for at least three years and valid for as
    long as you offer spare parts or customer support for that product
    model, to give anyone who possesses the object code either (1) a
    copy of the Corresponding Source for all the software in the
    product that is covered by this License, on a durable physical
    medium customarily used for software interchange, for a price no
    more than your reasonable cost of physically performing this
    conveying of source, or (2) access to copy the
    Corresponding Source from a network server at no charge.

    c) Convey individual copies of the object code with a copy of the
    written offer to provide the Corresponding Source.  This
    alternative is allowed only occasionally and noncommercially, and
    only if you received the object code with such an offer, in accord
    with subsection 6b.

    d) Convey the object code by offering access from a designated
    place (gratis or for a charge), and offer equivalent access to the
    Corresponding Source in the same way through the same place at no
    further charge.  You need not require recipients to copy the
    Corresponding Source along with the object code.  If the place to
    copy the object code is a network server, the Corresponding Source
    may be on a different server (operated by you or a third party)
    that supports equivalent copying facilities, provided you maintain
    clear directions next to the object code saying where to find the
    Corresponding Source.  Regardless of what server hosts the
    Corresponding Source, you remain obligated to ensure that it is
    available for as long as needed to satisfy these requirements.

    e) Convey the object code using peer-to-peer transmission, provided
    you inform other peers where the object code and Corresponding
    Source of the work are being offered to the general public at no
    charge under subsection 6d.

  A separable portion of the object code, whose source code is excluded
from the Corresponding Source as a System Library, need not be
included in conveying the object code work.

  A "User Product" is either (1) a "consumer product", which means any
tangible personal property which is normally used for personal, family,
or household purposes, or (2) anything designed or sold for incorporation
into a dwelling.  In determining whether a product is a consumer product,
doubtful cases shall be resolved in favor of coverage.  For a particular
product received by a particular user, "normally used" refers to a
typical or common use of that class of product, regardless of the status
of the particular user or of the way in which the particular user
actually uses, or expects or is expected to use, the product.  A product
is a consumer product regardless of whether the product has substantial
commercial, industrial or non-consumer uses, unless such uses represent
the only significant mode of use of the product.

  "Installation Information" for a User Product means any methods,
procedures, authorization keys, or other information required to install
and execute modified versions of a covered work in that User Product from
a modified version of its Corresponding Source.  The information must
suffice to ensure that the continued functioning of the modified object
code is in no case prevented or interfered with solely because
modification has been made.

  If you convey an object code work under this section in, or with, or
specifically for use in, a User Product, and the conveying occurs as
part of a transaction in which the right of possession and use of the
User Product is transferred to the recipient in perpetuity or for a
fixed term (regardless of how the transaction is characterized), the
Corresponding Source conveyed under this section must be accompanied
by the Installation Information.  But this requirement does not apply
if neither you nor any third party retains the ability to install
modified object code on the User Product (for example, the work has
been installed in ROM).

  The requirement to provide Installation Information does not include a
requirement to continue to provide support service, warranty, or updates
for a work that has been modified or installed by the recipient, or for
the User Product in which it has been modified or installed.  Access to a
network may be denied when the modification itself materially and
adversely affects the operation of the network or violates the rules and
protocols for communication across the network.

  Corresponding Source conveyed, and Installation Information provided,
in accord with this section must be in a format that is publicly
documented (and with an implementation available to the public in
source code form), and must require no special password or key for
unpacking, reading or copying.

  7. Additional Terms.

  "Additional permissions" are terms that supplement the terms of this
License by making exceptions from one or more of its conditions.
Additional permissions that are applicable to the entire Program shall
be treated as though they were included in this License, to the extent
that they are valid under applicable law.  If additional permissions
apply only to part of the Program, that part may be used separately
under those permissions, but the entire Program remains governed by
this License without regard to the additional permissions.

  When you convey a copy of a covered work, you may at your option
remove any additional permissions from that copy, or from any part of
it.  (Additional permissions may be written to require their own
removal in certain cases when you modify the work.)  You may place
additional permissions on material, added by you to a covered work,
for which you have or can give appropriate copyright permission.

  Notwithstanding any other provision of this License, for material you
add to a covered work, you may (if authorized by the copyright holders of
that material) supplement the terms of this License with terms:

    a) Disclaiming warranty or limiting liability differently from the
    terms of sections 15 and 16 of this License; or

    b) Requiring preservation of specified reasonable legal notices or
    author attributions in that material or in the Appropriate Legal
    Notices displayed by works containing it; or

    c) Prohibiting misrepresentation of the origin of that material, or
    requiring that modified versions of such material be marked in
    reasonable ways as different from the original version; or

    d) Limiting the use for publicity purposes of names of licensors or
    authors of the material; or

    e) Declining to grant rights under trademark law for use of some
    trade names, trademarks, or service marks; or

    f) Requiring indemnification of licensors and authors of that
    material by anyone who conveys the material (or modified versions of
    it) with contractual assumptions of liability to the recipient, for
    any liability that these contractual assumptions directly impose on
    those licensors and authors.

  All other non-permissive additional terms are considered "further
restrictions" within the meaning of section 10.  If the Program as you
received it, or any part of it, contains a notice stating that it is
governed by this License along with a term that is a further
restriction, you may remove that term.  If a license document contains
a further restriction but permits relicensing or conveying under this
License, you may add to a covered work material governed by the terms
of that license document, provided that the further restriction does
not survive such relicensing or conveying.

  If you add terms to a covered work in accord with this section, you
must place, in the relevant source files, a statement of the
additional terms that apply to those files, or a notice indicating
where to find the applicable terms.

  Additional terms, permissive or non-permissive, may be stated in the
form of a separately written license, or stated as exceptions;
the above requirements apply either way.

  8. Termination.

  You may not propagate or modify a covered work except as expressly
provided under this License.  Any attempt otherwise to propagate or
modify it is void, and will automatically terminate your rights under
this License (including any patent licenses granted under the third
paragraph of section 11).

  However, if you cease all violation of this License, then your
license from a particular copyright holder is reinstated (a)
provisionally, unless and until the copyright holder explicitly and
finally terminates your license, and (b) permanently, if the copyright
holder fails to notify you of the violation by some reasonable means
prior to 60 days after the cessation.

  Moreover, your license from a particular copyright holder is
reinstated permanently if the copyright holder notifies you of the
violation by some reasonable means, this is the first time you have
received notice of violation of this License (for any work) from that
copyright holder, and you cure the violation prior to 30 days after
your receipt of the notice.

  Termination of your rights under this section does not terminate the
licenses of parties who have received copies or rights from you under
this License.  If your rights have been terminated and not permanently
reinstated, you do not qualify to receive new licenses for the same
material under section 10.

  9. Acceptance Not Required for Having Copies.

  You are not required to accept this License in order to receive or
run a copy of the Program.  Ancillary propagation of a covered work
occurring solely as a consequence of using peer-to-peer transmission
to receive a copy likewise does not require acceptance.  However,
nothing other than this License grants you permission to propagate or
modify any covered work.  These actions infringe copyright if you do
not accept this License.  Therefore, by modifying or propagating a
covered work, you indicate your acceptance of this License to do so.

  10. Automatic Licensing of Downstream Recipients.

  Each time you convey a covered work, the recipient automatically
receives a license from the original licensors, to run, modify and
propagate that work, subject to this License.  You are not responsible
for enforcing compliance by third parties with this License.

  An "entity transaction" is a transaction transferring control of an
organization, or substantially all assets of one, or subdividing an
organization, or merging organizations.  If propagation of a covered
work results from an entity transaction, each party to that
transaction who receives a copy of the work also receives whatever
licenses to the work the party's predecessor in interest had or could
give under the previous paragraph, plus a right to possession of the
Corresponding Source of the work from the predecessor in interest, if
the predecessor has it or can get it with reasonable efforts.

  You may not impose any further restrictions on the exercise of the
rights granted or affirmed under this License.  For example, you may
not impose a license fee, royalty, or other charge for exercise of
rights granted under this License, and you may not initiate litigation
(including a cross-claim or counterclaim in a lawsuit) alleging that
any patent claim is infringed by making, using, selling, offering for
sale, or importing the Program or any portion of it.

  11. Patents.

  A "contributor" is a copyright holder who authorizes use under this
License of the Program or a work on which the Program is based.  The
work thus licensed is called the contributor's "contributor version".

  A contributor's "essential patent claims" are all patent claims
owned or controlled by the contributor, whether already acquired or
hereafter acquired, that would be infringed by some manner, permitted
by this License, of making, using, or selling its contributor version,
but do not include claims that would be infringed only as a
consequence of further modification of the contributor version.  For
purposes of this definition, "control" includes the right to grant
patent sublicenses in a manner consistent with the requirements of
this License.

  Each contributor grants you a non-exclusive, worldwide, royalty-free
patent license under the contributor's essential patent claims, to
make, use, sell, offer for sale, import and otherwise run, modify and
propagate the contents of its contributor version.

  In the following three paragraphs, a "patent license" is any express
agreement or commitment, however denominated, not to enforce a patent
(such as an express permission to practice a patent or covenant not to
sue for patent infringement).  To "grant" such a patent license to a
party means to make such an agreement or commitment not to enforce a
patent against the party.

  If you convey a covered work, knowingly relying on a patent license,
and the Corresponding Source of the work is not available for anyone
to copy, free of charge and under the terms of this License, through a
publicly available network server or other readily accessible means,
then you must either (1) cause the Corresponding Source to be so
available, or (2) arrange to deprive yourself of the benefit of the
patent license for this particular work, or (3) arrange, in a manner
consistent with the requirements of this License, to extend the patent
license to downstream recipients.  "Knowingly relying" means you have
actual knowledge that, but for the patent license, your conveying the
covered work in a country, or your recipient's use of the covered work
in a country, would infringe one or more identifiable patents in that
country that you have reason to believe are valid.

  If, pursuant to or in connection with a single transaction or
arrangement, you convey, or propagate by procuring conveyance of, a
covered work, and grant a patent license to some of the parties
receiving the covered work authorizing them to use, propagate, modify
or convey a specific copy of the covered work, then the patent license
you grant is automatically extended to all recipients of the covered
work and works based on it.

  A patent license is "discriminatory" if it does not include within
the scope of its coverage, prohibits the exercise of, or is
conditioned on the non-exercise of one or more of the rights that are
specifically granted under this License.  You may not convey a covered
work if you are a party to an arrangement with a third party that is
in the business of distributing software, under which you make payment
to the third party based on the extent of your activity of conveying
the work, and under which the third party grants, to any of the
parties who would receive the covered work from you, a discriminatory
patent license (a) in connection with copies of the covered work
conveyed by you (or copies made from those copies), or (b) primarily
for and in connection with specific products or compilations that
contain the covered work, unless you entered into that arrangement,
or that patent license was granted, prior to 28 March 2007.

  Nothing in this License shall be construed as excluding or limiting
any implied license or other defenses to infringement that may
otherwise be available to you under applicable patent law.

  12. No Surrender of Others' Freedom.

  If conditions are imposed on you (whether by court order, agreement or
otherwise) that contradict the conditions of this License, they do not
excuse you from the conditions of this License.  If you cannot convey a
covered work so as to satisfy simultaneously your obligations under this
License and any other pertinent obligations, then as a consequence you may
not convey it at all.  For example, if you agree to terms that obligate you
to collect a royalty for further conveying from those to whom you convey
the Program, the only way you could satisfy both those terms and this
License would be to refrain entirely from conveying the Program.

  13. Use with the GNU Affero General Public License.

  Notwithstanding any other provision of this License, you have
permission to link or combine any covered work with a work licensed
under version 3 of the GNU Affero General Public License into a single
combined work, and to convey the resulting work.  The terms of this
License will continue to apply to the part which is the covered work,
but the special requirements of the GNU Affero General Public License,
section 13, concerning interaction through a network will apply to the
combination as such.

  14. Revised Versions of this License.

  The Free Software Foundation may publish revised and/or new versions of
the GNU General Public License from time to time.  Such new versions will
be similar in spirit to the present version, but may differ in detail to
address new problems or concerns.

  Each version is given a distinguishing version number.  If the
Program specifies that a certain numbered version of the GNU General
Public License "or any later version" applies to it, you have the
option of following the terms and conditions either of that numbered
version or of any later version published by the Free Software
Foundation.  If the Program does not specify a version number of the
GNU General Public License, you may choose any version ever published
by the Free Software Foundation.

  If the Program specifies that a proxy can decide which future
versions of the GNU General Public License can be used, that proxy's
public statement of acceptance of a version permanently authorizes you
to choose that version for the Program.

  Later license versions may give you additional or different
permissions.  However, no additional obligations are imposed on any
author or copyright holder as a result of your choosing to follow a
later version.

  15. Disclaimer of Warranty.

  THERE IS NO WARRANTY FOR THE PROGRAM, TO THE EXTENT PERMITTED BY
APPLICABLE LAW.  EXCEPT WHEN OTHERWISE STATED IN WRITING THE COPYRIGHT
HOLDERS AND/OR OTHER PARTIES PROVIDE THE PROGRAM "AS IS" WITHOUT WARRANTY
OF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO,
THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
PURPOSE.  THE ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE PROGRAM
IS WITH YOU.  SHOULD THE PROGRAM PROVE DEFECTIVE, YOU ASSUME THE COST OF
ALL NECESSARY SERVICING, REPAIR OR CORRECTION.

  16. Limitation of Liability.

  IN NO EVENT UNLESS REQUIRED BY APPLICABLE LAW OR AGREED TO IN WRITING
WILL ANY COPYRIGHT HOLDER, OR ANY OTHER PARTY WHO MODIFIES AND/OR CONVEYS
THE PROGRAM AS PERMITTED ABOVE, BE LIABLE TO YOU FOR DAMAGES, INCLUDING ANY
GENERAL, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE
USE OR INABILITY TO USE THE PROGRAM (INCLUDING BUT NOT LIMITED TO LOSS OF
DATA OR DATA BEING RENDERED INACCURATE OR LOSSES SUSTAINED BY YOU OR THIRD
PARTIES OR A FAILURE OF THE PROGRAM TO OPERATE WITH ANY OTHER PROGRAMS),
EVEN IF SUCH HOLDER OR OTHER PARTY HAS BEEN ADVISED OF THE POSSIBILITY OF
SUCH DAMAGES.

  17. Interpretation of Sections 15 and 16.

  If the disclaimer of warranty and limitation of liability provided
above cannot be given local legal effect according to their terms,
reviewing courts shall apply local law that most closely approximates
an absolute waiver of all civil liability in connection with the
Program, unless a warranty or assumption of liability accompanies a
copy of the Program in return for a fee.

                     END OF TERMS AND CONDITIONS

            How to Apply These Terms to Your New Programs

  If you develop a new program, and you want it to be of the greatest
possible use to the public, the best way to achieve this is to make it
free software which everyone can redistribute and change under these terms.

  To do so, attach the following notices to the program.  It is safest
to attach them to the start of each source file to most effectively
state the exclusion of warranty; and each file should have at least
the "copyright" line and a pointer to where the full notice is found.

    <one line to give the program's name and a brief idea of what it does.>
    Copyright (C) <year>  <name of author>

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.

Also add information on how to contact you by electronic and paper mail.

  If the program does terminal interaction, make it output a short
notice like this when it starts in an interactive mode:

    <program>  Copyright (C) <year>  <name of author>
    This program comes with ABSOLUTELY NO WARRANTY; for details type `show w'.
    This is free software, and you are welcome to redistribute it
    under certain conditions; type `show c' for details.

The hypothetical commands `show w' and `show c' should show the appropriate
parts of the General Public License.  Of course, your program's commands
might be different; for a GUI interface, you would use an "about box".

  You should also get your employer (if you work as a programmer) or school,
if any, to sign a "copyright disclaimer" for the program, if necessary.
For more information on this, and how to apply and follow the GNU GPL, see
<http://www.gnu.org/licenses/>.

  The GNU General Public License does not permit incorporating your program
into proprietary programs.  If your program is a subroutine library, you
may consider it more useful to permit linking proprietary applications with
the library.  If this is what you want to do, use the GNU Lesser General
Public License instead of this License.  But first, please read
<http://www.gnu.org/philosophy/why-not-lgpl.html>.

# THATCH /packages/arc/pkgIndex.tcl 
# pkgIndex.tcl for additional tile pixmap theme arc.
#
# We don't provide the package is the image subdirectory isn't present,
# or we don't have the right version of Tcl/Tk
#
# To use this automatically within tile, the tile-using application should
# use tile::availableThemes and tile::setTheme 

if {![file isdirectory [file join $dir arc]]} { return }

package ifneeded ttk::theme::arc 0.1 \
    [list source [file join $dir arc.tcl]]

# vim:ts=8:sw=4:sts=4:et

# THATCH /packages/arc/pkgIndex.tcl 
package ifneeded ttk::theme::arc 0.1 \
    [list source [file join $dir arc.tcl]]
