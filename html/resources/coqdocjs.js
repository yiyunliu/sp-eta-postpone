var coqdocjs = coqdocjs || {};
(function(){

function toArray(nl){
    return Array.prototype.slice.call(nl);
}

function proofStatus(){
  var proofs = toArray(document.getElementsByClassName("proof"));
  if(proofs.length) {
    for(var proof of proofs) {
      if (proof.getAttribute("show") === "false") {
          return "some-hidden";
      }
    }
    return "all-shown";
  }
  else {
    return "no-proofs";
  }
}

function updateView(){
  document.getElementById("toggle-proofs").setAttribute("proof-status", proofStatus());
}

function foldProofs() {
  var hasCommands = true;
  var nodes = document.getElementsByClassName("command");
  for (const proof of document.getElementsByClassName("proof")) {
      proof.addEventListener("click", function(proof){return function(e){
        if (e.target.parentNode.tagName.toLowerCase() === "a")
          return;
        proof.setAttribute("show", proof.getAttribute("show") === "true" ? "false" : "true");
        proof.setAttribute("animate", "");
        updateView();
      };}(proof));
      proof.setAttribute("show", "false");
  }
}

function toggleProofs(){
  var someProofsHidden = proofStatus() === "some-hidden";
  toArray(document.getElementsByClassName("proof")).forEach(function(proof){
    proof.setAttribute("show", someProofsHidden);
    proof.setAttribute("animate", "");
  });
  updateView();
}

function fixTitle(){
  var url = "/" + window.location.pathname;
  var basename = url.substring(url.lastIndexOf('/')+1, url.lastIndexOf('.'));
  if (basename === "toc") {document.title = "Table of Contents";}
  else if (basename === "indexpage") {document.title = "Index";}
  else {document.title = basename;}
}

function postprocess(){
  foldProofs();
  document.getElementById("toggle-proofs").addEventListener("click", toggleProofs);
  updateView();
}

fixTitle();
document.addEventListener('DOMContentLoaded', postprocess);

coqdocjs.toggleProofs = toggleProofs;
})();
