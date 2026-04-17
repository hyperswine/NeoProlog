#!/usr/bin/env sol

file = "main.nprolog".
res = sh "neoprolog {file}".
echo res|stdout.
