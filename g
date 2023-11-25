#!/bin/sh

stack run my-hs-proj && \
    dot -Tpng graph.dot -o graph.png && \
    open graph.png
