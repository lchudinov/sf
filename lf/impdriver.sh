#!/bin/sh

ocamlc -w -20 -w -26 -o impdriver imp.mli imp.ml impdriver.ml -o ./impdriver
