// There is no civilized way to change the title of the Table of Contents
// so that it could be in Hebrew. The org-mode files do not provide for an
// abstraction that is suitable for work with different languages, so what 
// I do here is a hack: Just swap the text on the fly... Sorry! -mgg

toc = document.getElementById("text-table-of-contents").innerHTML;
document.getElementById("table-of-contents").innerHTML = 
  "<h2>תוכן הענינים</h2>" + toc;
