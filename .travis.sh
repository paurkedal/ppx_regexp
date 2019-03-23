#! /bin/sh
set -ex
cd `dirname $0`
sudo apt -y install m4
opam pin add -yn ${PKG_NAME} .
opam depext -y ${PKG_NAME}
opam install -yt ${PKG_NAME}
