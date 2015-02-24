var showingBox = false;

var hideOrShow = function() {
  var searchBox = document.getElementById("searchbox");
  var width = window.innerWidth;
  if (searchBox) {
    if ( width > 900 ) {
      if (! showingBox) {
        searchBox.style.display="inherit";
        showingBox = true;
      } 
    } else {
      if (showingBox) {
       searchBox.style.display="none";
       showingBox = false;
      }
    }
  }
};

hideOrShow();

window.addEventListener("resize", hideOrShow);
