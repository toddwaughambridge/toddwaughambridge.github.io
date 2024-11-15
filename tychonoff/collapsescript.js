function fun() {
    var content = document.getElementsByClassName("collapsiblecontent")[0];
    if (content.style.display === "block") {
      content.style.display = "none";
    } else {
      content.style.display = "block";
    }
  }
