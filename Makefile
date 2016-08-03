clean:
	find . -name '*.d' -or -name '*.clean' -or -name '*.olean' -or -name '*.ilean' -or -name '.ninja*' -or -name 'build.ninja' | xargs rm
