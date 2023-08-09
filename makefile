# makefile
# sync'ing the new website to www.little-lisper.org and to lvs.cs.bgu.ac.il
# 
# Programmer: Mayer Goldberg, 2011

# sshfs gmayer@little-lisper.org:html /mnt
# make mnt
# umount /mnt
mnt:
	rsync	-av \
		--recursive \
		--update \
		--copy-links \
		--chmod=a+r \
		--delete \
		--delete-after \
		../website \
		/mnt

lvs:
	rsync	-av \
		--recursive \
		--update \
		--copy-links \
		--chmod=a+r \
		--delete \
		--delete-after \
		../website \
		gmayer@lvs.cs.bgu.ac.il:html 

lvsll:
	rsync	-av \
		--recursive \
		--update \
		--copy-links \
		--delete \
		--delete-after \
		../website \
		gmayer@www.little-lisper.org:html 

