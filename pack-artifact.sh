#!/usr/bin/sh
set -xe

rm -rf artifact artifact.tar
git archive --prefix='artifact/' --format=tar HEAD | tar -xf -
tar --create --numeric-owner --file artifact.tar artifact
rm -r artifact
