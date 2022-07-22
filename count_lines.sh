# summarize line counts. Requires `cloc`, which can be installed with `sudo apt install cloc`.
cloc --by-file --include-lang=Lean src/cicm2022 --fullpath --not-match-d=src/cicm2022/examples
cloc --by-file --include-lang=Lean src/cicm2022/examples --fullpath --not-match-d=src/cicm2022/examples/Proj
cloc --by-file --include-lang=Lean src/cicm2022/examples/Proj
