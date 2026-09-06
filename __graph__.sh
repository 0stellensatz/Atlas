#!/usr/bin/env bash
#
# The knowledge web of this project, drawn from the sources on every run.
#
# Every reference to an `<Project>.Knowledge.<Term>` is one edge---from the file that
# refers to the item referred to---so the graph is a grep over the library tree and there
# is nothing to maintain beside the files themselves. Both link forms count, and that is
# the point: an `import` is a prerequisite, and a backticked fully-qualified name in a
# docstring is the softer reference, which may name an item that has not been written yet.
#
# Prerequisites are drawn above their dependents. A knowledge item is a box; a unit's
# questions is an ellipse, so the two layers are told apart at a glance. An item that is
# referred to but has no file is drawn in red, so the picture is the backlog as well---
# those red nodes are the whole of what tracks it.
#
# Writes graph.pdf, which is gitignored. Where graphviz is not installed it prints the DOT
# source instead and says so, which loses nothing: that source is the whole of what this
# script produces, and the renderer is interchangeable.
#
# ponytail: a reference is resolved to its item by file name only, so a name whose tail
# has been renamed away (`Knowledge.JumpSet.shift` after `shift` is gone) still resolves.
# Checking the tail would need the elaborated environment, since a structure's projections
# are nowhere in the text; `lake build` is what catches that, and catches it properly.

set -u
shopt -s nullglob
cd "$(dirname "$0")"

# The library's name as `lakefile.toml` gives it---not the name of the directory this script
# sits in, which need not carry it and in a git worktree does not. The selection is the one
# `__check__.py` makes, so the picture is of the library that gets checked: the `[[lean_lib]]`
# named in `defaultTargets` where there is one, that target's `roots` where it sets them, and
# the first target otherwise. Read by hand rather than by a TOML parser, so an array written
# across several lines is not seen. What is *not* done is falling back to the directory name---
# that is the bug, and a graph named for a branch is drawn over a tree that is not there---so a
# name that cannot be read is fatal here.
if [ ! -f lakefile.toml ]; then
    echo "error: $PWD is not a Lake project (no lakefile.toml)" >&2
    exit 1
fi
NAME=$(awk '
    function quoted(s) { sub(/^[^"]*"/, "", s); sub(/".*/, "", s); return s }
    /^[[:space:]]*defaultTargets[[:space:]]*=/ { want = $0 }
    /^[[:space:]]*\[\[lean_lib\]\]/            { n++; lib = 1; next }
    /^[[:space:]]*\[/                          { lib = 0 }
    lib && /^[[:space:]]*name[[:space:]]*=[[:space:]]*"/ {
        if (!(n in name)) name[n] = quoted($0)
    }
    lib && /^[[:space:]]*roots[[:space:]]*=[[:space:]]*\[[[:space:]]*"/ {
        if (!(n in root)) root[n] = quoted($0)
    }
    END {
        pick = 1
        for (i = 1; i <= n; i++)
            if (name[i] != "" && index(want, "\"" name[i] "\"")) { pick = i; break }
        chosen = root[pick] != "" ? root[pick] : name[pick]
        print chosen
    }
' lakefile.toml)
if [ -z "$NAME" ]; then
    echo "error: lakefile.toml names no [[lean_lib]] to draw" >&2
    exit 1
fi
LIB=$NAME

src=$(
    echo "digraph ${NAME}Knowledge {"
    echo '    rankdir=BT;'
    echo '    node [shape=box, fontname="Helvetica", fontsize=10];'
    echo '    edge [arrowsize=0.7, color=gray40];'

    find "$LIB" -name '*.lean' -not -path '*/.lake/*' | sort | while read -r f; do
        rel=${f#"$LIB"/}
        case $rel in
            Knowledge/*)
                node=${rel#Knowledge/}; node=${node%.lean}
                printf '    "%s";\n' "$node"
                ;;
            Questions/*)
                # One node per unit, not per file: Challenge and Development are two faces
                # of one unit, and both reach the same layer.
                node=${rel#Questions/}; node=${node%%/*}
                printf '    "%s" [shape=ellipse, style=filled, fillcolor=gray92];\n' "$node"
                ;;
            *)  node=${rel%.lean}
                printf '    "%s";\n' "$node"
                ;;
        esac

        # An item is referred to by its *module* name, whose components are UpperCamelCase
        # and so equal the file stem exactly. A lowercase component is a declaration
        # inside an item rather than the item, and is not an edge---requiring the initial
        # capital is what keeps a declaration reference out of the backlog.
        #
        # The two link forms are drawn differently, because they are different claims: an
        # `import` is a prerequisite and is solid, a docstring mention is the soft link and
        # is dashed. Only the solid edges are the dependency order, so only they have to be
        # acyclic---a pair of items naming each other in prose is normal and is not a cycle
        # in anything Lean cares about.
        imported=" $(grep -o "^import $NAME\\.Knowledge\\.[A-Z][A-Za-z0-9_]*" "$f" |
                         sed "s/^import $NAME\\.Knowledge\\.//" | sort -u | tr '\n' ' ')"
        for target in $(grep -o "$NAME\\.Knowledge\\.[A-Z][A-Za-z0-9_]*" "$f" |
                            sed "s/^$NAME\\.Knowledge\\.//" | sort -u); do
            [ "$target" = "$node" ] && continue          # a file naming itself is not an edge
            [ -f "$LIB/Knowledge/$target.lean" ] ||
                printf '    "%s" [color=red, fontcolor=red];\n' "$target"
            case $imported in
                *" $target "*) printf '    "%s" -> "%s";\n' "$node" "$target" ;;
                *) printf '    "%s" -> "%s" [style=dashed, constraint=false];\n' "$node" "$target" ;;
            esac
        done
    done | sort -u

    echo '}'
)

if command -v dot > /dev/null; then
    printf '%s\n' "$src" | dot -Tpdf -o graph.pdf && echo "graph.pdf"
else
    printf '%s\n' "$src"
    echo "graphviz not installed (brew install graphviz); printed the DOT source instead" >&2
fi
