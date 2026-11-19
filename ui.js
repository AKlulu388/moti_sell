
/* ============ UI（v14 设计） ============ */
(function(){
"use strict";
var eng=MT.createEngine({storage:window.localStorage,fetch:window.fetch.bind(window),noSeed:true});
try{eng.init();}catch(e){console.error('init error',e);}
window.mtEng=eng;
var $=function(id){return document.getElementById(id);};
var lastQ='',lastK=[],lastIds=[],curDetail=-1,curCat='',curSubj='',jsonCands=[],editIdx=-1;
function esc(s){return String(s==null?'':s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');}
function optWidth(s){
  var t=MT.tex2readable(String(s)),w=0;
  for(var i=0;i<t.length;i++){w+=t.charCodeAt(i)>0x2e80?2:1;}
  return w;
}
function formatStem(s){
  var lines=String(s==null?'':s).split(/\r?\n/);
  var html='',opts=[],optsRaw=[];
  function flush(){
    if(!opts.length)return;
    var maxW=0;optsRaw.forEach(function(o){var w=optWidth(o);if(w>maxW)maxW=w;});
    var cls=maxW<=6?'opts-4':(maxW<=24?'opts-2':'opts-1');
    html+='<div class="opts '+cls+'">'+opts.map(function(o){return '<div class="opt">'+o+'</div>';}).join('')+'</div>';
    opts=[];optsRaw=[];
  }
  lines.forEach(function(ln){
    var t=ln.trim();if(!t)return;
    if(/^[A-D][\.、．\)]/.test(t)){opts.push(mx(t));optsRaw.push(t);return;}
    flush();html+='<div class="stem-line">'+mx(t)+'</div>';
  });
  flush();
  return html||mx(s);
}
/* ZIP 读取 + 图片解析库（纯JS，离线，兼容老WebView） */
function mtUtf8(b){var s='',i=0;while(i<b.length){var c=b[i++];if(c<128)s+=String.fromCharCode(c);else if(c<224){s+=String.fromCharCode(((c&31)<<6)|(b[i++]&63));}else if(c<240){s+=String.fromCharCode(((c&15)<<12)|((b[i++]&63)<<6)|(b[i++]&63));}else{var cp=((c&7)<<18)|((b[i++]&63)<<12)|((b[i++]&63)<<6)|(b[i++]&63);cp-=65536;s+=String.fromCharCode(55296+(cp>>10),56320+(cp&1023));}}return s;}
function mtInflate(src){
  var pos=0,bitbuf=0,bitcnt=0,out=[];
  function bits(n){while(bitcnt<n){if(pos>=src.length)throw new Error('inflate: 数据不足');bitbuf|=src[pos++]<<bitcnt;bitcnt+=8;}var v=bitbuf&((1<<n)-1);bitbuf>>>=n;bitcnt-=n;return v;}
  function build(lengths){var counts=[],symbols=[],n=lengths.length,i;for(i=0;i<=15;i++)counts[i]=0;for(i=0;i<n;i++)counts[lengths[i]]++;counts[0]=0;var offs=[];offs[1]=0;for(i=1;i<15;i++)offs[i+1]=offs[i]+counts[i];for(i=0;i<n;i++)if(lengths[i])symbols[offs[lengths[i]]++]=i;return {counts:counts,symbols:symbols};}
  function decode(h){var code=0,first=0,index=0,len;for(len=1;len<=15;len++){code|=bits(1);var count=h.counts[len];if(code-first<count)return h.symbols[index+(code-first)];index+=count;first=(first+count)<<1;code<<=1;}throw new Error('inflate: 坏 Huffman 码');}
  var LBASE=[3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258];
  var LEXT=[0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0];
  var DBASE=[1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577];
  var DEXT=[0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13];
  function codes(lh,dh){for(;;){var sym=decode(lh);if(sym<256){out.push(sym);}else if(sym===256){return;}else{sym-=257;if(sym>=29)throw new Error('inflate: 坏长度码');var len=LBASE[sym]+bits(LEXT[sym]);var ds=decode(dh);if(ds>=30)throw new Error('inflate: 坏距离码');var dist=DBASE[ds]+bits(DEXT[ds]);if(dist>out.length)throw new Error('inflate: 距离越界');for(var i=0;i<len;i++)out.push(out[out.length-dist]);}}}
  for(;;){var final=bits(1),type=bits(2);
    if(type===0){bitbuf=0;bitcnt=0;if(pos+4>src.length)throw new Error('inflate: stored 头不足');var len=src[pos]|(src[pos+1]<<8);pos+=4;if(pos+len>src.length)throw new Error('inflate: stored 数据不足');for(var i=0;i<len;i++)out.push(src[pos++]);}
    else if(type===1){var ll=[],dl=[],i;for(i=0;i<144;i++)ll[i]=8;for(;i<256;i++)ll[i]=9;for(;i<280;i++)ll[i]=7;for(;i<288;i++)ll[i]=8;for(i=0;i<32;i++)dl[i]=5;codes(build(ll),build(dl));}
    else if(type===2){var order=[16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15];var hlit=bits(5)+257,hdist=bits(5)+1,hclen=bits(4)+4;var cl=[];for(var i=0;i<19;i++)cl[i]=0;for(i=0;i<hclen;i++)cl[order[i]]=bits(3);var ch=build(cl);var lengths=[],i=0;while(i<hlit+hdist){var s=decode(ch);if(s<16){lengths[i++]=s;}else if(s===16){if(i===0)throw new Error('inflate: 16 无前值');var prev=lengths[i-1],rep=3+bits(2);for(var j=0;j<rep;j++)lengths[i++]=prev;}else if(s===17){var rep=3+bits(3);for(var j=0;j<rep;j++)lengths[i++]=0;}else{var rep=11+bits(7);for(var j=0;j<rep;j++)lengths[i++]=0;}}
      if(i>hlit+hdist)throw new Error('inflate: 长度表溢出');codes(build(lengths.slice(0,hlit)),build(lengths.slice(hlit,hlit+hdist)));}
    else throw new Error('inflate: 坏块类型');
    if(final)break;}
  return new Uint8Array(out);
}
function mtParseZip(buf){
  var ab=buf instanceof ArrayBuffer?buf:buf.buffer.slice(buf.byteOffset,buf.byteOffset+buf.byteLength);
  var b=new Uint8Array(ab),dv=new DataView(ab);
  var eocd=-1,start=Math.max(0,b.length-65557);
  for(var i=b.length-22;i>=start;i--){if(dv.getUint32(i,true)===0x06054b50){eocd=i;break;}}
  if(eocd<0)throw new Error('不是有效的 ZIP 文件');
  var n=dv.getUint16(eocd+10,true),cd=dv.getUint32(eocd+16,true);
  var entries=[],p=cd;
  for(var k=0;k<n;k++){
    if(dv.getUint32(p,true)!==0x02014b50)throw new Error('ZIP 中央目录损坏');
    var method=dv.getUint16(p+10,true),csize=dv.getUint32(p+20,true),nl=dv.getUint16(p+28,true),el=dv.getUint16(p+30,true),cl=dv.getUint16(p+32,true),lo=dv.getUint32(p+42,true);
    var name=mtUtf8(b.subarray(p+46,p+46+nl));
    if(dv.getUint32(lo,true)!==0x04034b50)throw new Error('ZIP 局部头损坏');
    var lnl=dv.getUint16(lo+26,true),lel=dv.getUint16(lo+28,true);
    var data=b.subarray(lo+30+lnl+lel,lo+30+lnl+lel+csize);
    var content=method===0?data:method===8?mtInflate(data):null;
    if(content===null)throw new Error('不支持的压缩方式: '+method);
    entries.push({name:name,data:content});
    p+=46+nl+el+cl;
  }
  return entries;
}
function mtBytesToDataUrl(bytes,mime){
  var bin='',CH=8192;
  for(var i=0;i<bytes.length;i+=CH)bin+=String.fromCharCode.apply(null,bytes.subarray(i,i+CH));
  return 'data:'+mime+';base64,'+btoa(bin);
}
function mtResolveMdImages(text,fileMap){
  var replaced=0,missing=[];
  var out=String(text).replace(/!\[([^\]]*)\]\(([^)\s]+)\)/g,function(m,alt,path){
    if(/^(data:|https?:\/\/)/i.test(path))return m;
    var clean=decodeURIComponent(path).replace(/^\.\//,'');
    var base=clean.split('/').pop();
    var hit=fileMap[clean]||fileMap[base];
    if(!hit){missing.push(path);return m;}
    replaced++;
    return '!['+alt+']('+hit+')';
  });
  return {text:out,replaced:replaced,missing:missing};
}


function mtLoadImg(url){return new Promise(function(res,rej){var im=new Image();im.onload=function(){res(im);};im.onerror=function(){rej(new Error('图片解码失败'));};im.src=url;});}
function mtEncodeImg(im,maxW,fmt,q){var scale=Math.min(1,maxW/im.width);var c=document.createElement('canvas');c.width=Math.max(1,Math.round(im.width*scale));c.height=Math.max(1,Math.round(im.height*scale));c.getContext('2d').drawImage(im,0,0,c.width,c.height);return c.toDataURL(fmt,q);}
function mtCompress(text,maxW,fmt,q,encodeFn){
  maxW=maxW||800;fmt=fmt||'image/jpeg';q=q||0.85;
  var re=/data:image\/(?:png|jpeg|jpg|gif|webp);base64,[A-Za-z0-9+/=]+/g;
  var src=String(text),matches=src.match(re)||[],before=src.length,uniq={};
  matches.forEach(function(u){uniq[u]=1;});
  var keys=Object.keys(uniq),map={},chain=Promise.resolve();
  keys.forEach(function(u){chain=chain.then(function(){
    var p=encodeFn?encodeFn(u):mtLoadImg(u).then(function(im){return mtEncodeImg(im,maxW,fmt,q);});
    return p.then(function(nu){if(nu&&nu.length<u.length)map[u]=nu;}).catch(function(){});
  });});
  return chain.then(function(){
    var out=src.replace(re,function(u){return map[u]||u;});
    return {text:out,before:before,after:out.length,count:keys.length,shrunk:Object.keys(map).length};
  });
}
function mtImportZip(buf,compress){
  var entries=mtParseZip(buf),imgMap={},mds=[],jsons=[];
  entries.forEach(function(e){
    var n=e.name.toLowerCase();
    if(/\.(png|jpe?g|gif|webp)$/.test(n)){var mime=/\.png$/.test(n)?'image/png':/\.gif$/.test(n)?'image/gif':/\.webp$/.test(n)?'image/webp':'image/jpeg';var url=mtBytesToDataUrl(e.data,mime);imgMap[e.name]=url;var base=e.name.split('/').pop();if(!imgMap[base])imgMap[base]=url;}
    else if(/\.(md|markdown|txt)$/.test(n))mds.push(e);
    else if(/\.json$/.test(n))jsons.push(e);
  });
  if(!mds.length&&!jsons.length)throw new Error('ZIP 里没有 md/txt 试卷或 json 题库');
  var report=[],chain=Promise.resolve();
  mds.forEach(function(e){chain=chain.then(function(){
    var r=mtResolveMdImages(mtUtf8(e.data),imgMap);
    var p=compress?mtCompress(r.text,800,'image/jpeg',0.85):Promise.resolve({text:r.text,before:r.text.length,after:r.text.length});
    return p.then(function(c){ingestPaper(c.text);report.push(e.name+'：内嵌图'+r.replaced+'张'+(r.missing.length?'，缺失'+r.missing.join(','):'')+(compress?'，压缩省'+Math.max(0,Math.round((c.before-c.after)/1024))+'KB':''));});
  });});
  jsons.forEach(function(e){chain=chain.then(function(){
    var r=mtResolveMdImages(mtUtf8(e.data),imgMap);
    var p=compress?mtCompress(r.text,800,'image/jpeg',0.85):Promise.resolve({text:r.text});
    return p.then(function(c){$('jsonText').value=c.text;report.push(e.name+'：内嵌图'+r.replaced+'张，点「解析并预览」入库');});
  });});
  return chain.then(function(){return report;});
}
function mtHandleZip(fileInput,statEl){
  var f=fileInput.files[0];fileInput.value='';if(!f)return;
  statEl.textContent='解包中…';
  var rd=new FileReader();
  rd.onload=function(){mtImportZip(rd.result,$('zipCompress').checked).then(function(rep){statEl.textContent=rep.join('；');toast('ZIP 导入完成');}).catch(function(e){statEl.textContent='失败：'+e.message;toast('ZIP 导入失败');});};
  rd.readAsArrayBuffer(f);
}
$('btnPickZip').onclick=function(){$('zipFile').click();};
$('zipFile').onchange=function(){mtHandleZip(this,$('zipStat'));};
$('btnPickJsonZip').onclick=function(){$('jsonZipFile').click();};
$('jsonZipFile').onchange=function(){mtHandleZip(this,$('jsonStat'));};
$('btnImgTool').onclick=function(){
  var files=$('imgToolFile').files;if(!files.length){toast('请先选择图片');return;}
  var res=[],done=0;
  Array.prototype.forEach.call(files,function(f){
    var im=new Image();
    im.onload=function(){var mw=parseInt($('imgToolWidth').value,10)||800;res.push('![图]('+mtEncodeImg(im,mw,$('imgToolFmt').value,0.85)+')');done++;if(done===files.length){$('imgToolOut').value=res.join('\n');toast('已生成 '+res.length+' 张，约'+Math.round(res.join('').length*0.75/1024)+'KB');}URL.revokeObjectURL(im.src);};
    im.onerror=function(){done++;toast('有图片解码失败');};
    im.src=URL.createObjectURL(f);
  });
};
$('btnImgToolCopy').onclick=function(){var t=$('imgToolOut').value;if(!t){toast('请先生成代码');return;}copyText(t);};
$('btnImgToolInsert').onclick=function(){var t=$('imgToolOut').value;if(!t){toast('请先生成代码');return;}$('paperText').value=($('paperText').value?$('paperText').value+'\n':'')+t;toast('已追加到试卷文本');};
$('btnCompressPaper').onclick=function(){
  var t=$('paperText').value;
  if(!/data:image\//.test(t)){toast('试卷文本里没有内嵌图片');return;}
  $('compressStat').textContent='压缩中…';
  mtCompress(t,800,'image/jpeg',0.85).then(function(r){$('paperText').value=r.text;$('compressStat').textContent=r.count+'张图：'+Math.round(r.before/1024)+'KB→'+Math.round(r.after/1024)+'KB';toast('压缩完成');});
};
window.mtZip={parse:mtParseZip,resolve:mtResolveMdImages,inflate:mtInflate};
window.mtUtf8=mtUtf8;window.mtImportZip=mtImportZip;window.mtCompress=mtCompress;

function imgSplit(s){
  var re=/!\[([^\]]*)\]\(([^)\s]+)\)/g,out='',last=0,m;
  while((m=re.exec(s))){
    out+=esc(s.slice(last,m.index));
    var src=m[2];
    if(/^(data:image\/(png|jpeg|jpg|gif|webp);base64,[A-Za-z0-9+/=]+|https?:\/\/[^\s"'<>]+)$/i.test(src))out+='<img class="qimg" loading="lazy" decoding="async" alt="'+esc(m[1])+'" src="'+src+'">';
    else out+=esc(m[0]);
    last=m.index+m[0].length;
  }
  return out+esc(s.slice(last));
}
function renderMathHTML(s){
  if(s==null)return '';
  var str=String(s);
  if(typeof katex==='undefined')return imgSplit(MT.tex2readable(str));
  var re=/(\$\$[\s\S]+?\$\$|\\\[[\s\S]+?\\\]|\\\([\s\S]+?\\\)|\$[^$]+?\$)/g;
  var out='',last=0,m;
  while((m=re.exec(str))){
    out+=imgSplit(str.slice(last,m.index));
    var seg=m[0],display=false,latex;
    if(seg.indexOf('$$')===0){display=true;latex=seg.slice(2,-2);}
    else if(seg.indexOf('\\[')===0){display=true;latex=seg.slice(2,-2);}
    else if(seg.indexOf('\\(')===0){latex=seg.slice(2,-2);}
    else{latex=seg.slice(1,-1);}
    try{out+=katex.renderToString(latex,{throwOnError:false,displayMode:display,strict:false});}
    catch(e){out+=esc(MT.tex2readable(seg));}
    last=m.index+seg.length;
  }
  out+=imgSplit(str.slice(last));
  return out;
}
function mx(s){return renderMathHTML(s);}
function toast(msg){var t=$('toast');t.textContent=msg;t.classList.add('on');clearTimeout(t._h);t._h=setTimeout(function(){t.classList.remove('on');},2600);}
function copyText(txt){
  if(navigator.clipboard&&navigator.clipboard.writeText){navigator.clipboard.writeText(txt).then(function(){toast('已复制');},function(){fallbackCopy(txt);});}
  else fallbackCopy(txt);
}
function fallbackCopy(txt){
  var ta=document.createElement('textarea');ta.value=txt;document.body.appendChild(ta);ta.select();
  try{document.execCommand('copy');toast('已复制');}catch(e){toast('复制失败，请长按文本全选');}
  ta.remove();
}
function utf8b64(text){return btoa(unescape(encodeURIComponent(text)));}
function blobDownload(name,text,mime){
  try{
    var blob=new Blob([text],{type:mime||'application/json'});
    var a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=name;
    document.body.appendChild(a);a.click();a.remove();
    toast('已触发下载：'+name);
  }catch(e){toast('下载不可用，请用导出面板复制');}
}
function saveTextFile(name,text,mime){
  if(window.Android&&window.Android.saveFile){
    try{window.Android.saveFile(name,utf8b64(text));toast('已保存到手机「下载」目录：'+name);return;}catch(e){}
  }
  try{
    var file=new File([text],name,{type:mime||'application/json'});
    if(navigator.canShare&&navigator.canShare({files:[file]})){
      navigator.share({files:[file],title:name}).then(function(){toast('已通过系统分享保存');},function(){blobDownload(name,text,mime);});
      return;
    }
  }catch(e){}
  blobDownload(name,text,mime);
}
function readFile(file,cb){var rd=new FileReader();rd.onload=function(){cb(rd.result);};rd.readAsText(file);}

/* ---- 题库 ---- */
function chapters(){
  var map={};eng.motifs.forEach(function(m){var c=m.chapter||'未分类';map[c]=(map[c]||0)+1;});
  return map;
}
function renderBank(){
  $('hdrCount').textContent=eng.motifs.length+' 母题';
  $('stTypes').textContent=eng.motifs.length;
  $('stMoves').textContent=eng.motifs.filter(function(m){return m.moveName&&m.moveName!=='无';}).length;
  $('stSamples').textContent=eng.samples.length;
  var ch=chapters(),cats=Object.keys(ch);
  $('catCount').textContent=cats.length+' 类';
  var tagH='<button class="tagbtn'+(curCat===''?' on':'')+'" data-cat="">全部 '+eng.motifs.length+'</button>';
  cats.forEach(function(c){tagH+='<button class="tagbtn'+(curCat===c?' on':'')+'" data-cat="'+esc(c)+'">'+esc(c)+' '+ch[c]+'</button>';});
  $('subjectFilter').innerHTML=tagH;
  $('catList').innerHTML=tagH;
  document.querySelectorAll('#subjectFilter .tagbtn,#catList .tagbtn').forEach(function(b){
    b.onclick=function(){curCat=b.dataset.cat;renderBank();};
  });
  var subjOrder=['数学','物理','化学','生物','政治','历史','地理','英语','语文'];
  var subjCount={};eng.motifs.forEach(function(m){var s=m.subject||'其他';subjCount[s]=(subjCount[s]||0)+1;});
  var subjs=Object.keys(subjCount).sort(function(a,b){var ia=subjOrder.indexOf(a),ib=subjOrder.indexOf(b);return (ia<0?99:ia)-(ib<0?99:ib);});
  var sTagH='<button class="tagbtn'+(curSubj===''?' on':'')+'" data-subj="">全部学科 '+eng.motifs.length+'</button>';
  subjs.forEach(function(s){sTagH+='<button class="tagbtn'+(curSubj===s?' on':'')+'" data-subj="'+esc(s)+'">'+esc(s)+' '+subjCount[s]+'</button>';});
  $('subjFilter').innerHTML=sTagH;
  document.querySelectorAll('#subjFilter .tagbtn').forEach(function(b){b.onclick=function(){curSubj=b.dataset.subj;renderBank();};});
  var kw=($('q').value||'').trim().toLowerCase();
  var list=[];
  eng.motifs.forEach(function(m,i){
    if(curCat&&(m.chapter||'未分类')!==curCat)return;
    if(curSubj&&(m.subject||'其他')!==curSubj)return;
    if(kw){
      var hay=(m.name+' '+(m.triggers||[]).join(' ')+' '+(m.moveName||'')+' '+(m.move||'')+' '+(m.chapter||'')).toLowerCase();
      if(hay.indexOf(kw)<0)return;
    }
    list.push(i);
  });
  $('listCount').textContent=list.length+' 条';
  var groups={};list.forEach(function(i){var s=eng.motifs[i].subject||'其他';(groups[s]=groups[s]||[]).push(i);});
  var html='';
  subjs.forEach(function(s){
    var gi=groups[s];if(!gi||!gi.length)return;
    html+='<div class="subj-head">'+esc(s)+'<span class="cnt">'+gi.length+' 条</span></div>';
    gi.forEach(function(i){
      var m=eng.motifs[i];
      html+='<div class="item'+(curDetail===i?' on':'')+'" data-i="'+i+'"><div class="it-h"><span class="idx">'+(i+1)+'</span><span class="t">'+esc(m.name)+'</span></div>'+
        '<div class="m"><span class="mini">'+esc(m.chapter||'未分类')+'</span><span class="mini gray">'+esc(m.difficulty||'')+'</span>'+
        (m.moveName&&m.moveName!=='无'?'<span class="mini teal">'+esc(m.moveName)+'</span>':'')+'</div></div>';
    });
  });
  $('typeList').innerHTML=html||'<div class="empty">没有匹配的母题</div>';
  document.querySelectorAll('#typeList .item').forEach(function(el){
    el.onclick=function(){openDetail(parseInt(el.dataset.i,10));};
  });
  refreshCatalogSubjects();
}
function detailHTML(i){
  var m=eng.motifs[i];
  var h='<div class="detail-h"><h1>'+esc(m.name)+'</h1><div class="kv">'+
    '<span class="mini acc">'+esc(m.chapter||'未分类')+'</span><span class="mini">'+esc(m.subject||'数学')+'</span><span class="mini gray">'+esc(m.difficulty||'')+'</span>'+
    (m.moveName&&m.moveName!=='无'?'<span class="mini teal">大招 · '+esc(m.moveName)+'</span>':'')+'</div></div>';
  if(m.triggers&&m.triggers.length)h+='<div class="sec"><div class="sec-t">识别特征</div><div class="trg">'+m.triggers.map(function(t){return '<span class="pill">'+mx(t)+'</span>';}).join('')+'</div></div>';
  if(m.rules&&m.rules.length)h+='<div class="sec"><div class="sec-t">识别判据</div><div class="trg">'+m.rules.map(function(t){return '<span class="pill k">'+mx(t)+'</span>';}).join('')+'</div></div>';
  if(m.move&&m.moveName&&m.moveName!=='无')h+='<div class="sec g"><div class="sec-t">解法大招</div><div class="movebox"><div class="mn">'+esc(m.moveName)+'</div><div class="mc">'+mx(m.move)+'</div></div></div>';
  if(m.solution&&m.solution.length)h+='<div class="sec"><div class="sec-t">解法步骤</div><ol class="steps">'+m.solution.map(function(s,j){return '<li><span class="num">'+(j+1)+'</span><p>'+mx(s)+'</p></li>';}).join('')+'</ol></div>';
  if(m.keyPoints&&m.keyPoints.length)h+='<div class="sec"><div class="sec-t">关键点</div><div class="note">'+m.keyPoints.map(mx).join('<br>')+'</div></div>';
  if(m.caveat&&m.caveat.length)h+='<div class="sec"><div class="sec-t">易错警示</div><div class="note warn">'+m.caveat.map(mx).join('<br>')+'</div></div>';
  if(m.sampleQuestion)h+='<div class="sec"><div class="sec-t">例题</div><div class="fx">'+mx(m.sampleQuestion)+'</div></div>';
  if(m.highFrequencyFormula&&m.highFrequencyFormula.length)h+='<div class="sec"><div class="sec-t">高频公式</div>'+m.highFrequencyFormula.map(function(f){return '<div class="fx" style="margin-bottom:6px">'+mx(f)+'</div>';}).join('')+'</div>';
  h+='<div class="sec"><button class="btn sm" id="btnEditMotif">编辑此母题</button> <button class="btn dgr sm" id="btnDelMotif">删除此母题</button><span class="hint" style="margin-left:8px">编辑会重新学习该母题特征；删除同步清理样本与缓存</span></div>';
  return h;
}
function isWideBank(){return !!(window.matchMedia&&window.matchMedia('(min-width:900px)').matches&&$('view-bank').classList.contains('on'));}
function bindDetailBtns(host,i){
  var be=host.querySelector('#btnEditMotif');if(be)be.onclick=function(){openEditForm(i);};
  var bd=host.querySelector('#btnDelMotif');if(bd)bd.onclick=function(){
    if(confirm('确定删除母题「'+eng.motifs[i].name+'」？相关学习样本与缓存会同步清理。')){
      var nm=eng.deleteMotif(i);
      document.body.classList.remove('detail-open');$('detailOverlay').classList.remove('on');
      if($('detailDock'))$('detailDock').innerHTML='<div class="empty">点击左侧题型，在此查看解法详情</div>';
      curDetail=-1;renderBank();renderMe();toast('已删除：'+nm);
    }
  };
}
function openDetail(i){
  curDetail=i;
  if(isWideBank()){
    $('detail').innerHTML='';
    $('detailDock').innerHTML=detailHTML(i);
    bindDetailBtns($('detailDock'),i);
    $('detailOverlay').classList.remove('on');document.body.classList.remove('detail-open');
    renderBank();return;
  }
  if($('detailDock'))$('detailDock').innerHTML='<div class="empty">点击左侧题型，在此查看解法详情</div>';
  $('detail').innerHTML=detailHTML(i);
  bindDetailBtns($('detail'),i);
  $('backTitle').textContent=eng.motifs[i].name;
  document.body.classList.add('detail-open');
  var ov=$('detailOverlay');ov.classList.add('on');ov.scrollTop=0;
  renderBank();
}
$('btnDockClose').onclick=function(){$('detailDock').innerHTML='<div class="empty">点击左侧题型，在此查看解法详情</div>';curDetail=-1;renderBank();};
$('btnBack').onclick=function(){document.body.classList.remove('detail-open');$('detailOverlay').classList.remove('on');curDetail=-1;renderBank();};
$('q').oninput=function(){renderBank();};

/* ---- 识题（v14 行工作流） ---- */
var rowsData=[];try{rowsData=JSON.parse(window.localStorage.getItem('mt.rows')||'[]');}catch(e){rowsData=[];}
var rowFilter='all';
function rowPassFilter(row){
  if(rowFilter==='all')return true;
  var r=row.result;
  if(rowFilter==='done')return !!r;
  if(rowFilter==='hit')return !!(r&&r.ids&&r.ids.length);
  if(rowFilter==='pick')return !!(r&&!(r.ids&&r.ids.length)&&(r.source==='pick'||r.source==='offline-none'));
  return true;
}
var pickTarget=-1,matching=false;
function saveRows(){try{window.localStorage.setItem('mt.rows',JSON.stringify(rowsData));}catch(e){}}
function srcLabel(r){
  var map={'cache':'缓存 · 0token','local':'本地 · 0token','sig':'已学映射','ai+nn':'DeepSeek+本地','pick':'待确认','nn-only':'离线低置信','need_key':'需Key','empty':'题库为空','rematch':'考点重配 · 0token','offline-none':'离线未命中','ai-type':'AI直判·库内精确'};
  return map[r.source]||r.source;
}
function renderSummary(){
  var done=0,hit=0,pick=0;
  rowsData.forEach(function(row){if(row.result){done++;if(row.result.ids&&row.result.ids.length)hit++;else if(row.result.source==='pick')pick++;}});
  $('smTotal').textContent=rowsData.length;$('smDone').textContent=done;$('smHit').textContent=hit;$('smPick').textContent=pick;
  $('libCount').textContent=eng.motifs.length;
  document.querySelectorAll('#matchSummary .stat').forEach(function(s){s.classList.toggle('on',s.dataset.filter===rowFilter);});
  updateBatchEstimate();
}
function updateBatchEstimate(){
  var el=$('batchEstimate');if(!el)return;
  var qs=rowsData.filter(function(r){return (r.stem||'').trim()&&!r.result;}).map(function(r){return {no:r.no,sub:r.sub||0,sub2:r.sub2||'',stem:r.stem,parent:r.parent||''};});
  if(!rowsData.length){el.textContent='上传试卷或生成题号后，点「预估整卷花费」先算钱再匹配。';return;}
  if(!qs.length){el.textContent='全部题目已有结果，无需再花费。';return;}
  var mode=eng.settings.recMode||'hybrid';
  if(mode==='offline'){el.textContent='离线模式：全部本地判定，0 token（未命中的题给候选，人工勾选即学会）。';return;}
  var e=eng.estimateBatchRows(qs,mode);
  el.textContent=(mode==='ai'?'AI模式：':'')+'待识别 '+e.needApi+' 小问需 DeepSeek，合并为 '+e.requests+' 次请求（'+e.free+' 题可本地免费判）：预估输入 '+e.inputTokens+' token + 输出约 '+e.outputTokensEst+' token，约 ¥'+e.costEst.toFixed(4)+'（'+(e.peak?'高峰':'空闲')+'价，上限估算）';
}
function rowResultHTML(row,idx){
  var r=row.result;
  var aiBlock='';
  if(row.aiLoading)aiBlock='<div class="empty" style="margin-top:8px">AI详解生成中…（耗token）</div>';
  else if(row.aiSolution)aiBlock='<div class="ai-sol" style="margin-top:8px"><div class="sec-t">AI详解本题（已保存）</div><div class="note">'+mx(row.aiSolution.text).replace(/\n/g,'<br>')+'</div><p class="hint">'+row.aiSolution.tokens+' token · 约¥'+row.aiSolution.costEst.toFixed(4)+'</p></div>';
  if(!r)return (row.error?'<div class="notice a" style="margin-top:8px">'+esc(row.error)+'</div>':'')+aiBlock;
  var h='<div class="verdict" style="margin-top:8px">';
  h+='<div class="vline"><b>'+srcLabel(r)+'</b>'+(r.tokens?' · '+r.tokens+' token':'')+(r.confidence?' · 置信 '+r.confidence.toFixed(2):'')+(r.costEst!==undefined?' · 离线预估输入'+r.estInput+'/实际'+r.promptTokens+(r.cacheHit?'(命中'+r.cacheHit+')':'')+' · 约¥'+r.costEst.toFixed(4):'')+'</div>';
  if(r.kaodian&&r.kaodian.length){
    var w=row.kpW||r.kaodian.map(function(){return 1;});
    h+='<div class="trg">'+r.kaodian.map(function(k,j){
      var wj=w[j]===undefined?1:w[j];
      var cls=wj===0?'pill':'pill k';
      var style=wj===0?' style="text-decoration:line-through;opacity:.55;cursor:pointer"':(wj===2?' style="cursor:pointer;font-weight:800"':' style="cursor:pointer"');
      return '<span class="'+cls+'"'+style+' data-kpw="'+idx+'-'+j+'">'+(wj===2?'★':'')+mx(k)+(wj===0?'（已排除）':'')+'</span>';
    }).join('')+'</div>';
    h+='<div class="actbar" style="margin-top:6px"><div class="field" style="flex:1 1 120px"><input data-kpadd="'+idx+'" placeholder="自行添加考点"></div><button class="btn sm" data-kpaddbtn="'+idx+'">添加</button><button class="btn sm pri" data-rematch="'+idx+'">按考点重配(0token)</button></div>';
    h+='<p class="hint">点考点标签切换权重：正常→★重点→排除；调整后点「按考点重配」，本地网络按你的考点重新判，不花token。</p>';
  }
  if(r.ids&&r.ids.length){
    r.ids.forEach(function(i){var m=eng.motifs[i];if(!m)return;
      h+='<div class="vline" data-solmotif="'+i+'" data-solrow="'+idx+'" style="cursor:pointer"><b>'+esc(m.name)+'</b> <span class="mini gray">'+esc(m.chapter||'')+'</span> <span class="mini acc">点击看解法详情 ›</span></div>';
      if(m.moveName&&m.moveName!=='无'&&m.move)h+='<div class="vmove"><b>'+esc(m.moveName)+'</b> '+mx(m.move)+'</div>';});
    if(r.combo)h+='<div class="vline warn">组合题 · '+r.ids.length+' 个母题叠加</div>';
  }
  if((r.source==='pick'||r.source==='offline-none')&&r.candidates&&r.candidates.length){
    h+='<div class="cands">'+r.candidates.map(function(c){
      return '<label class="candPick"><input type="checkbox" data-cand="'+idx+'-'+c.id+'" style="width:18px;height:18px;accent-color:var(--pri)"><span>'+esc(c.name)+'</span><span class="conf '+(c.score>=0.5?'h':(c.score>=0.3?'m':'l'))+'">'+c.score.toFixed(2)+'</span></label>';}).join('')+
      '</div><div class="actbar" style="margin-top:8px"><button class="btn sm pri" data-pickconfirm="'+idx+'">确认并学习</button></div>';
  }
  if(r.source==='need_key')h+='<div class="vline warn">请先到「我的」填入 DeepSeek API Key</div>';
  return h+'</div>'+aiBlock;
}
function renderRows(){
  var __html='';rowsData.forEach(function(row,idx){if(!rowPassFilter(row))return;
    var r=row.result;
    var target=r?((r.ids&&r.ids.length)?r.ids[0]:((r.candidates&&r.candidates.length)?r.candidates[0].id:-1)):-1;
    var conf=r?(r.ids&&r.ids.length?'<span class="conf h">命中 ›</span>':((r.source==='pick'||r.source==='offline-none')?'<span class="conf l">待确认 ›</span>':'<span class="conf m">'+srcLabel(r)+' ›</span>')):'<span class="conf l">未识别</span>';
    var bad=r&&(!r.ids||!r.ids.length)&&r.source!=='pick'&&r.source!=='offline-none';
    var headAttr=target>=0?' data-headopen="'+target+'" data-headrow="'+idx+'" style="cursor:pointer"':'';
    __html+='<div class="qrow'+(bad?' qrow-bad':'')+'">'+
      '<div class="qrow-head"'+headAttr+'><span class="qno" data-qno="'+idx+'" style="cursor:pointer" title="点击修改题号">'+rowLabel(row)+'</span><span class="mini gray" data-sec="'+idx+'" style="cursor:pointer" title="点击修改题型">'+esc(row.section||'题型?')+'</span>'+conf+'<span class="qhead-txt">'+(r?srcLabel(r):'')+(target>=0?' · 点击看解法':'')+'</span></div>'+
      '<div class="qbody"><div class="qcell">'+
      '<details class="stemdet"><summary style="font-size:13px;color:var(--ink2);cursor:pointer">'+esc((row.stem?MT.tex2readable(row.stem):'(空题干，点开填写)').slice(0,60))+((row.stem||'').length>60?'…':'')+'</summary>'+
      (row.stem?'<div class="stem-render" style="margin-top:8px">'+formatStem(row.stem)+'</div>':'')+
      '<div class="field" style="margin-top:8px"><textarea data-stem="'+idx+'" style="min-height:80px">'+esc(row.stem||'')+'</textarea></div></details>'+
      rowResultHTML(row,idx)+
      '<div class="qrow-actions" style="padding:8px 0 0">'+
      '<button class="btn sm" data-run="'+idx+'">识别</button>'+
      '<button class="btn sm" data-force="'+idx+'">DeepSeek重审</button>'+
      (r&&r.ids&&r.ids.length?'<button class="btn sm green" data-ok="'+idx+'">✓ 正确</button>':'')+
      (r&&r.ids&&r.ids.length?'<button class="btn sm" data-sol="'+idx+'">📖 解法</button>':'')+
      ((row.stem||'').trim()?'<button class="btn sm" data-ai="'+idx+'">🤖 AI详解</button>':'')+
      '<button class="btn sm" data-fix="'+idx+'">✗ 改判</button>'+
      '<button class="btn sm ghost" data-mergeup="'+idx+'" title="把本行题干并入上一行">⤴ 并入上题</button>'+
      '<button class="btn sm ghost" data-split="'+idx+'" title="按标记把本行拆成两行">✂ 拆分</button>'+
      '<button class="btn sm ghost" data-del="'+idx+'">删除</button>'+
      '</div></div></div></div>';
  });
  $('rows').innerHTML=__html||'<div class="empty">'+(rowsData.length?'当前筛选下没有题目，点「总题数」看全部':'还没有题号：输入 1-12 生成，或上传/粘贴试卷自动切题')+'</div>';
  document.querySelectorAll('#rows [data-stem]').forEach(function(t){t.oninput=function(){rowsData[parseInt(t.dataset.stem,10)].stem=t.value;saveRows();};});
  document.querySelectorAll('#rows [data-run]').forEach(function(b){b.onclick=function(){matchRow(parseInt(b.dataset.run,10),false);};});
  document.querySelectorAll('#rows [data-force]').forEach(function(b){b.onclick=function(){matchRow(parseInt(b.dataset.force,10),true);};});
  document.querySelectorAll('#rows [data-ok]').forEach(function(b){b.onclick=function(){var idx=parseInt(b.dataset.ok,10),row=rowsData[idx];eng.confirm(row.stem,row.result.ids,kpOf(row));row.result={source:'cache',ids:row.result.ids,kaodian:row.result.kaodian||[],tokens:0,combo:row.result.ids.length>1};saveRows();renderRows();renderMe();toast('已巩固记忆');};});
  document.querySelectorAll('#rows [data-fix]').forEach(function(b){b.onclick=function(){var idx=parseInt(b.dataset.fix,10);pickTarget=idx;openPick(rowsData[idx].result&&rowsData[idx].result.ids||[]);};});
  document.querySelectorAll('#rows [data-del]').forEach(function(b){b.onclick=function(){rowsData.splice(parseInt(b.dataset.del,10),1);saveRows();renderRows();};});
  document.querySelectorAll('#rows [data-qno]').forEach(function(el){el.onclick=function(e){e.stopPropagation();var idx=parseInt(el.dataset.qno,10);var row=rowsData[idx];
    var v=prompt('修改题号（支持 15、15(2)、15(2)①）：',rowLabel(row));if(v===null)return;
    var m=String(v).trim().match(/^(\d{1,3})(?:\((\d{1,2})\))?(.*)$/);
    if(!m){toast('题号格式不对');return;}
    row.no=parseInt(m[1],10);row.sub=m[2]?parseInt(m[2],10):0;row.sub2=(m[3]||'').trim();row.result=null;
    rowsData.sort(function(a,b){return a.no-b.no||(a.sub||0)-(b.sub||0)||String(a.sub2||'').localeCompare(String(b.sub2||''));});
    saveRows();renderRows();toast('题号已改为 '+rowLabel(row));};});
  document.querySelectorAll('#rows [data-sec]').forEach(function(el){el.onclick=function(e){e.stopPropagation();var idx=parseInt(el.dataset.sec,10);var row=rowsData[idx];
    var v=prompt('题型（单选/多选/选择/填空/解答/实验）：',row.section||'解答');if(v===null)return;
    v=String(v).trim();if(['单选','多选','选择','填空','解答','实验'].indexOf(v)<0){toast('题型须为：单选/多选/选择/填空/解答/实验');return;}
    row.section=v;saveRows();renderRows();toast('题型已改为 '+v);};});
  document.querySelectorAll('#rows [data-mergeup]').forEach(function(b){b.onclick=function(){var idx=parseInt(b.dataset.mergeup,10);
    if(idx<=0){toast('已是第一行，无法并入上题');return;}
    var row=rowsData[idx],prev=rowsData[idx-1];
    prev.stem=(prev.stem?prev.stem+'\n':'')+(row.stem||'');prev.result=null;prev.error='';
    rowsData.splice(idx,1);saveRows();renderRows();toast('已并入第 '+rowLabel(prev)+' 题，可重新识别');};});
  document.querySelectorAll('#rows [data-split]').forEach(function(b){b.onclick=function(){var idx=parseInt(b.dataset.split,10);var row=rowsData[idx];
    var stem=row.stem||'';if(!stem.trim()){toast('题干为空');return;}
    var mark=prompt('输入拆分标记，从该处拆出新行（如 (2) 或 ① 或某段文字）：','(2)');if(mark===null||mark==='')return;
    var pos=stem.indexOf(mark,1);if(pos<0){toast('题干中未找到该标记');return;}
    var orig=stem;var pre=stem.slice(0,pos).replace(/\s+$/,'');var post=stem.slice(pos);
    var numRe=/^\s*(?:第\s*(\d{1,3})\s*题|(\d{1,3})\s*[\.、．\)])\s*/;
    var numM=post.match(numRe);
    row.stem=pre.replace(numRe,'');row.result=null;row.error='';
    if(numM){
      var newNo=parseInt(numM[1]||numM[2],10);
      rowsData.push({no:newNo,sub:0,sub2:'',stem:post.replace(numM[0],''),section:row.section,parent:'',result:null});
      rowsData.sort(function(a,b){return a.no-b.no||(a.sub||0)-(b.sub||0)||String(a.sub2||'').localeCompare(String(b.sub2||''));});
      saveRows();renderRows();toast('已拆出独立的第 '+newNo+' 题');return;
    }
    if(!row.sub)row.sub=1;
    var maxSub=0;rowsData.forEach(function(r){if(r.no===row.no&&(r.sub||0)>maxSub)maxSub=r.sub;});
    row.parent=orig;
    rowsData.push({no:row.no,sub:maxSub+1,sub2:'',stem:post,section:row.section,parent:orig,result:null});
    rowsData.sort(function(a,b){return a.no-b.no||(a.sub||0)-(b.sub||0)||String(a.sub2||'').localeCompare(String(b.sub2||''));});
    saveRows();renderRows();toast('已拆分为 '+row.no+'('+row.sub+') 与 '+row.no+'('+(maxSub+1)+')');};});
  document.querySelectorAll('#rows [data-pickconfirm]').forEach(function(b){b.onclick=function(){
    var idx=parseInt(b.dataset.pickconfirm,10);var ids=[];
    document.querySelectorAll('#rows input[data-cand^="'+idx+'-"]:checked').forEach(function(c){ids.push(parseInt(c.dataset.cand.split('-')[1],10));});
    if(!ids.length){toast('至少勾选一个母题');return;}
    applyPick(idx,ids);};});
  document.querySelectorAll('#rows [data-kpw]').forEach(function(el){el.onclick=function(){
    var p=el.dataset.kpw.split('-'),idx=parseInt(p[0],10),j=parseInt(p[1],10),row=rowsData[idx];
    if(!row.kpW)row.kpW=row.result.kaodian.map(function(){return 1;});
    row.kpW[j]=row.kpW[j]===1?2:(row.kpW[j]===2?0:1);
    saveRows();renderRows();
  };});
  document.querySelectorAll('#rows [data-kpaddbtn]').forEach(function(b){b.onclick=function(){
    var idx=parseInt(b.dataset.kpaddbtn,10),row=rowsData[idx];
    var inp=document.querySelector('#rows input[data-kpadd="'+idx+'"]');
    var v=(inp.value||'').trim();if(!v){toast('先输入考点');return;}
    if(!row.kpW)row.kpW=row.result.kaodian.map(function(){return 1;});
    row.result.kaodian.push(v);row.kpW.push(1);
    inp.value='';saveRows();renderRows();toast('已添加考点：'+v);
  };});
  document.querySelectorAll('#rows [data-rematch]').forEach(function(b){b.onclick=function(){
    var idx=parseInt(b.dataset.rematch,10),row=rowsData[idx];
    var k=row.result.kaodian,w=row.kpW||k.map(function(){return 1;});
    var r=eng.rematchKaodian(k,w);
    var kept=[],keptW=[];
    for(var i=0;i<k.length;i++){var wi=w[i]===undefined?1:w[i];if(wi>0){kept.push(k[i]);keptW.push(wi);}}
    row.result={source:'rematch',ids:r.ids,kaodian:kept,candidates:r.candidates,tokens:0,combo:r.ids.length>1,confidence:r.max};
    row.kpW=keptW;
    saveRows();renderRows();toast('已按你的考点重新匹配（0 token）');
  };});
  document.querySelectorAll('#rows [data-open]').forEach(function(el){el.onclick=function(){switchView('bank');openDetail(parseInt(el.dataset.open,10));};});
  document.querySelectorAll('#rows [data-headopen]').forEach(function(el){el.onclick=function(){var idx=parseInt(el.dataset.headrow,10);var row=rowsData[idx];if(row&&row.result&&row.result.ids&&row.result.ids.length){openSolution(row.result.ids,row.stem,idx);}else{switchView('bank');openDetail(parseInt(el.dataset.headopen,10));}};});
  document.querySelectorAll('#rows [data-sol]').forEach(function(b){b.onclick=function(){var idx=parseInt(b.dataset.sol,10);var row=rowsData[idx];openSolution(row.result.ids,row.stem,idx);};});
  document.querySelectorAll('#rows [data-solmotif]').forEach(function(el){el.onclick=function(){var mi=parseInt(el.dataset.solmotif,10);var idx=parseInt(el.dataset.solrow,10);var row=rowsData[idx];openSolution([mi],row?row.stem:'',idx);};});
  document.querySelectorAll('#rows [data-ai]').forEach(function(b){b.onclick=function(){aiSolveRow(parseInt(b.dataset.ai,10));};});
  renderSummary();
}
function kpOf(row){
  var k=(row.result&&row.result.kaodian)||[],w=row.kpW;
  return k.filter(function(_,i){return !w||w[i]===undefined||w[i]>0;});
}
function applyPick(idx,ids){
  var row=rowsData[idx],k=kpOf(row);
  eng.confirm(row.stem,ids,k);
  row.result={source:'cache',ids:ids,kaodian:k,tokens:0,combo:ids.length>1};
  saveRows();renderRows();renderMe();
  toast(ids.length>1?'组合已确认，下次认识':'已学会，下次认识');
}
function matchRow(idx,force){return matchRowObj(rowsData[idx],force,idx);}
function matchRowObj(row,force,idx){
  var stem=(row.stem||'').trim();
  if(!stem){toast('第 '+rowLabel(row)+' 题题干为空');return Promise.resolve();}
  row.error='';row.result=null;renderRows();
  return eng.recognize(stem,{forceApi:!!force,mode:eng.settings.recMode}).then(function(r){row.result=r;saveRows();renderRows();renderMe();if(idx!==undefined&&r.ids&&r.ids.length&&eng.settings.autoSolution){openSolution(r.ids,stem,idx);}})
    .catch(function(e){row.error=String(e.message||e);saveRows();renderRows();});
}
function rowLabel(r){return r.no+(r.sub?'('+r.sub+')':'')+(r.sub2||'');}
function ensureRow(no,stem,sub,section,sub2,parent){
  sub=sub||0;sub2=sub2||'';
  for(var i=0;i<rowsData.length;i++){if(rowsData[i].no===no&&(rowsData[i].sub||0)===sub&&(rowsData[i].sub2||'')===sub2){if(stem){rowsData[i].stem=stem;rowsData[i].result=null;}if(section)rowsData[i].section=section;if(parent)rowsData[i].parent=parent;return;}}
  rowsData.push({no:no,sub:sub,sub2:sub2,stem:stem||'',section:section||'',parent:parent||'',result:null});
}
$('btnMakeRows').onclick=function(){
  var nos=MT.parseQnos($('qnos').value);
  if(!nos.length){toast('先填题号，如 1-12、15');return;}
  nos.forEach(function(n){ensureRow(n,'',0,'','','');});
  rowsData.sort(function(a,b){return a.no-b.no||(a.sub||0)-(b.sub||0)||String(a.sub2||'').localeCompare(String(b.sub2||''));});
  saveRows();renderRows();toast('已生成 '+nos.length+' 个题号');
};
$('btnPickPaper').onclick=function(){$('paperFile').click();};
$('btnDropPaper').onclick=function(){
  if(!rowsData.length&&!$('paperText').value){toast('当前没有导入的试卷');return;}
  if(confirm('删除已导入的试卷？将清空全部题目行与粘贴文本。')){
    rowsData=[];saveRows();renderRows();$('paperText').value='';$('qnos').value='';toast('已删除导入试卷');
  }
};
$('paperFile').onchange=function(){var f=this.files[0];if(!f)return;readFile(f,function(t){ingestPaper(t);});this.value='';};
$('btnParsePaper').onclick=function(){ingestPaper($('paperText').value);};
function ingestPaper(text){
  var parts=MT.splitPaper(text);
  if(!parts.length){toast('未解析出题目');return;}
  if($('splitSub').checked)parts=MT.expandSubs(parts);
  parts.forEach(function(p){ensureRow(p.no,p.stem,p.sub,p.section,p.sub2,p.parent);});
  rowsData.sort(function(a,b){return a.no-b.no||(a.sub||0)-(b.sub||0)||String(a.sub2||'').localeCompare(String(b.sub2||''));});
  saveRows();renderRows();toast('已切分 '+parts.length+' 题'+($('splitSub').checked?'（含小题）':''));
}
$('btnClearRows').onclick=function(){if(confirm('清空全部题目行？')){rowsData=[];saveRows();renderRows();}};
$('btnEstimate').onclick=function(){updateBatchEstimate();toast('已按当前峰谷价预估');};
$('btnMatch').onclick=function(){
  if(matching){toast('正在匹配中…');return;}
  var todo=[];rowsData.forEach(function(row){if((!row.result||row.error)&&(row.stem||'').trim())todo.push(row);});
  if(!todo.length){toast('没有待识别的题目');return;}
  matching=true;
  var total=todo.length,doneN=0,prog=$('matchProgress');
  function showProg(txt){prog.style.display='';$('mprogText').textContent=txt;$('mprogBar').style.width=Math.round(doneN/total*100)+'%';}
  showProg('匹配中 0/'+total+'（可切换其他模块，后台继续）');
  var groups=[],gmap={},singles=[];
  todo.forEach(function(row){
    if(row.sub){
      if(!gmap[row.no]){gmap[row.no]={no:row.no,rows:[],parent:''};groups.push(gmap[row.no]);}
      gmap[row.no].rows.push(row);if(row.parent)gmap[row.no].parent=row.parent;
    }else{singles.push(row);}
  });
  eng.setDeferTrain(true);
  var gi=0,singleDone=false;
  function fin(){
    $('mprogBar').style.width='100%';$('mprogText').textContent='识别完成，整理学习中…';
    eng.setDeferTrain(false).then(function(){matching=false;prog.style.display='none';toast('批量匹配完成');renderMe();});
  }
  function doSingles(cb){
    if(!singles.length){cb();return;}
    if(singles.length===1||eng.settings.batchSingles===false){
      var si=0;
      function nextS(){
        if(si>=singles.length){cb();return;}
        matchRowObj(singles[si++],false).then(function(){doneN++;showProg('匹配中 '+doneN+'/'+total+'（可切换其他模块，后台继续）');setTimeout(nextS,300);});
      }
      nextS();return;
    }
    var items=singles.map(function(r){return {label:String(r.no),stem:r.stem,row:r};});
    singles.forEach(function(r){r.error='';r.result=null;});
    renderRows();
    eng.recognizeBatch(items,{mode:eng.settings.recMode}).then(function(rs){
      rs.forEach(function(r,j){items[j].row.result=r;});
      doneN+=singles.length;showProg('匹配中 '+doneN+'/'+total+'（可切换其他模块，后台继续）');
      saveRows();renderRows();renderMe();cb();
    }).catch(function(e){
      singles.forEach(function(r){r.error=String(e.message||e);});
      doneN+=singles.length;showProg('匹配中 '+doneN+'/'+total);
      saveRows();renderRows();cb();
    });
  }
  function nextGroup(){
    if(gi>=groups.length){fin();return;}
    var g=groups[gi++];
    var subRows=g.rows.filter(function(r){return r.sub;});
    var canGroup=subRows.length>=2&&g.parent&&eng.settings.recMode!=='offline';
    if(canGroup){
      var subs=subRows.map(function(r){return {label:'('+r.sub+')'+(r.sub2||''),stem:r.stem,row:r};});
      subRows.forEach(function(r){r.error='';r.result=null;});
      renderRows();
      eng.recognizeGroup(g.parent,subs,{mode:eng.settings.recMode}).then(function(rs){
        rs.forEach(function(r,j){subs[j].row.result=r;});
        doneN+=subRows.length;showProg('匹配中 '+doneN+'/'+total+'（可切换其他模块，后台继续）');
        saveRows();renderRows();renderMe();setTimeout(nextGroup,300);
      }).catch(function(e){
        subRows.forEach(function(r){r.error=String(e.message||e);});
        doneN+=subRows.length;showProg('匹配中 '+doneN+'/'+total);
        saveRows();renderRows();setTimeout(nextGroup,300);
      });
    }else{
      var ii=0;
      function nextSub(){
        if(ii>=g.rows.length){setTimeout(nextGroup,300);return;}
        var row=g.rows[ii++];
        matchRowObj(row,false).then(function(){doneN++;showProg('匹配中 '+doneN+'/'+total+'（可切换其他模块，后台继续）');setTimeout(nextSub,300);});
      }
      nextSub();
    }
  }
  doSingles(function(){nextGroup();});
};
$('btnExpandAll').onclick=function(){
  var ds=document.querySelectorAll('#rows .stemdet');
  var open=ds.length&&ds[0].open;
  ds.forEach(function(d){d.open=!open;});
};
$('btnDelUnmatched').onclick=function(){
  var before=rowsData.length;
  rowsData=rowsData.filter(function(row){return !(row.result&&(!row.result.ids||!row.result.ids.length)&&row.result.source!=='pick');});
  saveRows();renderRows();toast('已删除 '+(before-rowsData.length)+' 行未匹配');
};
function buildResultMd(mode){
  var lines=['# 母题识别结果',''];
  rowsData.forEach(function(row){
    var r=row.result;
    if(!r){lines.push(rowLabel(row)+'. 未识别');if(mode==='full'&&row.stem)lines.push('   题目：'+MT.tex2readable(row.stem).replace(/\n/g,' '));return;}
    var names=(r.ids||[]).map(function(i){return eng.motifs[i]?eng.motifs[i].name:'?';});
    var moves=(r.ids||[]).map(function(i){var m=eng.motifs[i];return m&&m.moveName&&m.moveName!=='无'?m.moveName:'';}).filter(Boolean);
    lines.push(rowLabel(row)+'. 母题：'+(names.join(' + ')||'未匹配')+((r.source==='pick'||r.source==='offline-none')?'（待确认）':''));
    if(mode==='full'&&row.stem)lines.push('   题目：'+MT.tex2readable(row.stem).replace(/\n/g,' '));
    if(r.kaodian&&r.kaodian.length)lines.push('   知识点：'+r.kaodian.join('、'));
    if(moves.length)lines.push('   大招：'+moves.join(' / '));
  });
  return lines.join('\n');
}
$('btnExportResult').onclick=function(){var md=buildResultMd($('resultMode').value);$('resultMd').value=md;openExport('导出识别结果',md,'母题识别结果.md');};
$('btnCopyResult').onclick=function(){$('resultMd').value=buildResultMd($('resultMode').value);copyText($('resultMd').value);};
$('btnDownloadResult').onclick=function(){$('resultMd').value=buildResultMd($('resultMode').value);saveTextFile('母题识别结果.md',$('resultMd').value,'text/plain');};
function openPick(cur){
  $('pickList').innerHTML=eng.motifs.map(function(m,i){
    return '<label class="pickitem'+(cur.indexOf(i)>=0?' on':'')+'"><input type="checkbox" data-i="'+i+'"'+(cur.indexOf(i)>=0?' checked':'')+' style="width:18px;height:18px;accent-color:var(--pri)"><span>'+esc(m.name)+'</span><span class="mini gray">'+esc(m.chapter||'')+'</span></label>';
  }).join('');
  $('pickMask').classList.add('on');
}
$('btnPickCancel').onclick=function(){$('pickMask').classList.remove('on');pickTarget=-1;};
$('btnPickOk').onclick=function(){
  var ids=[];document.querySelectorAll('#pickList input:checked').forEach(function(c){ids.push(parseInt(c.dataset.i,10));});
  if(!ids.length){toast('至少选一个母题');return;}
  $('pickMask').classList.remove('on');
  if(pickTarget>=0){applyPick(pickTarget,ids);pickTarget=-1;}
};

/* ---- 录入 ---- */
function openEditForm(i){
  editIdx=i;var m=eng.motifs[i];
  $('intakeTitle').textContent='编辑母题';
  $('fName').value=m.name||'';$('fSubject').value=m.subject||'';$('fChapter').value=m.chapter||'';
  $('fDiff').value=m.difficulty||'中档';$('fSample').value=m.sampleQuestion||'';
  $('fTrig').value=(m.triggers||[]).join('，');$('fRules').value=(m.rules||[]).join('，');
  $('fSol').value=(m.solution||[]).join('\n');$('fMoveName').value=m.moveName||'';
  $('fMove').value=m.move||'';$('fKey').value=(m.keyPoints||[]).join('\n');
  $('fCaveat').value=(m.caveat||[]).join('\n');$('fFormula').value=(m.highFrequencyFormula||[]).join('\n');
  document.querySelector('#intakeTabs .sub-tab[data-pane="form"]').click();
  $('intakeMask').classList.add('on');
}
$('btnIntakeTab').onclick=function(){editIdx=-1;$('intakeTitle').textContent='录入母题';$('bridgeText').value=eng.getBridgePrompt();updateBridgeTok();$('intakeMask').classList.add('on');};
$('btnCloseIntake').onclick=function(){$('intakeMask').classList.remove('on');};
document.querySelectorAll('#intakeTabs .sub-tab').forEach(function(b){
  b.onclick=function(){
    document.querySelectorAll('#intakeTabs .sub-tab').forEach(function(x){x.classList.remove('on');});
    document.querySelectorAll('#intakeMask .pane').forEach(function(x){x.classList.remove('on');});
    b.classList.add('on');
    document.querySelector('#intakeMask .pane[data-pane="'+b.dataset.pane+'"]').classList.add('on');
  };
});
function showJsonCands(arr){
  jsonCands=arr;
  $('jsonStat').textContent='解析到 '+arr.length+' 条';
  $('jsonCandWrap').innerHTML=arr.map(function(m,i){
    return '<div class="cand"><div class="cand-h"><input type="checkbox" data-i="'+i+'" checked><b>'+esc(m.name||'(缺名称)')+'</b>'+
      '<span class="mini">'+esc(m.chapter||'')+'</span>'+(m.moveName&&m.moveName!=='无'?'<span class="mini teal">'+esc(m.moveName)+'</span>':'')+
      (!m.name?'<span class="mini amb">缺 name 将跳过</span>':'')+'</div></div>';
  }).join('');
  $('btnSaveJsonCands').style.display=arr.length?'':'none';
}
$('btnPickJson').onclick=function(){$('jsonFile').click();};
$('jsonFile').onchange=function(){var f=this.files[0];if(!f)return;readFile(f,function(t){$('jsonText').value=t;parseJsonText();});this.value='';};
function parseJsonText(){
  try{
    var d=JSON.parse($('jsonText').value);
    var arr=Array.isArray(d)?d:(d&&Array.isArray(d.motifs)?d.motifs:null);
    if(!arr)throw new Error('应为母题数组');
    showJsonCands(arr);
  }catch(e){toast('JSON 解析失败：'+e.message);}
}
$('btnParseJson').onclick=parseJsonText;
$('btnClearJson').onclick=function(){$('jsonText').value='';$('jsonCandWrap').innerHTML='';$('jsonStat').textContent='';$('btnSaveJsonCands').style.display='none';};
$('btnSaveJsonCands').onclick=function(){
  var sel=[];document.querySelectorAll('#jsonCandWrap input:checked').forEach(function(c){sel.push(jsonCands[parseInt(c.dataset.i,10)]);});
  if(!sel.length){toast('未选择任何母题');return;}
  try{
    var r=eng.importMotifs(sel,{overwrite:$('jsonOverwrite').checked});
    toast('新增 '+r.added+' 条，更新 '+r.updated+' 条，跳过 '+r.skipped+' 条');
    $('intakeMask').classList.remove('on');
    $('jsonCandWrap').innerHTML='';$('btnSaveJsonCands').style.display='none';
    renderBank();renderMe();
  }catch(e){toast(e.message);}
};
$('btnSaveForm').onclick=function(){
  try{
    function lines(id){return $(id).value.split('\n').map(function(s){return s.trim();}).filter(Boolean);}
    function commas(id){return $(id).value.split(/[,，]/).map(function(s){return s.trim();}).filter(Boolean);}
    var mobj={name:$('fName').value.trim(),subject:$('fSubject').value.trim()||'数学',chapter:$('fChapter').value.trim(),
      difficulty:$('fDiff').value,sampleQuestion:$('fSample').value.trim(),triggers:commas('fTrig'),rules:commas('fRules'),
      solution:lines('fSol'),moveName:$('fMoveName').value.trim()||'无',move:$('fMove').value.trim(),
      keyPoints:lines('fKey'),caveat:lines('fCaveat'),highFrequencyFormula:lines('fFormula'),source:$('fSource').value.trim()||'手动录入'};
    if(editIdx>=0){eng.updateMotif(editIdx,mobj);toast('已保存修改并重新学习');editIdx=-1;$('intakeTitle').textContent='录入母题';document.body.classList.remove('detail-open');$('detailOverlay').classList.remove('on');}
    else{eng.addMotif(mobj);toast('已入库并学会');}
    $('intakeMask').classList.remove('on');
    ['fName','fSample','fTrig','fRules','fSol','fMoveName','fMove','fKey','fCaveat','fFormula'].forEach(function(id){$(id).value='';});
    renderBank();renderMe();
  }catch(e){toast(e.message);}
};
$('btnSavePrompt').onclick=function(){eng.setBridgePrompt($('bridgeText').value.trim());updateBridgeTok();toast('提示词已保存');};
$('btnResetPrompt').onclick=function(){eng.resetBridgePrompt();$('bridgeText').value=eng.getBridgePrompt();updateBridgeTok();toast('已恢复默认');};
$('btnCopyPrompt').onclick=function(){copyText($('bridgeText').value);};
$('btnOpenPrompt').onclick=function(){
  $('bridgeText').value=eng.getBridgePrompt();updateBridgeTok();
  $('intakeMask').classList.add('on');
  document.querySelector('#intakeTabs .sub-tab[data-pane="prompt"]').click();
};

/* ---- 我的 ---- */
function renderMe(){
  $('meTypes').textContent=eng.motifs.length+' 条';
  $('meSamples').textContent=eng.samples.length+' 条';
  $('meCombo').textContent=eng.comboCount()+' 组';
  $('meLocal').textContent=eng.stats.localHits+eng.stats.sigHits;
  $('meCache').textContent=eng.stats.cacheHits;
  $('meApi').textContent=eng.stats.apiCalls;
  $('meTokens').textContent=eng.stats.tokensUsed;
  $('meSaved').textContent=eng.tokensSavedEst();
  $('meCost').textContent='¥'+(eng.stats.costEst||0).toFixed(4);
  $('meSavedMoney').textContent='¥'+eng.moneySaved().toFixed(4);
  $('spanPeak').textContent=(eng.isPeakNow()?'高峰时段 ×1':'空闲时段 ×0.5')+'（未命中'+eng.settings.priceIn+'/命中'+(eng.settings.priceHit||0)+'/输出'+eng.settings.priceOut+' 元/百万token）';
  $('priceIn').value=eng.settings.priceIn;
  $('priceOut').value=eng.settings.priceOut;
  $('priceHit').value=eng.settings.priceHit||0;
  var srvT=(eng.stats.srvHit||0)+(eng.stats.srvMiss||0);
  $('meSrvHit').textContent=srvT?Math.round((eng.stats.srvHit||0)/srvT*100)+'%（'+(eng.stats.srvHit||0)+'/'+srvT+' token）':'—（尚无API调用）';
  $('apiKey').value=eng.settings.apiKey;
  $('model').value=eng.settings.model;
  $('threshold').value=eng.settings.localThreshold;
  $('thVal').textContent=Number(eng.settings.localThreshold).toFixed(2);
  $('autoSolution').checked=eng.settings.autoSolution!==false;
  $('deepThinking').checked=!!eng.settings.deepThinking;
  $('autoTrain').checked=eng.settings.autoTrain!==false;
  $('batchSingles').checked=eng.settings.batchSingles!==false;
}
function openExport(title,text,fname){
  $('exTitle').textContent=title;$('exText').value=text;
  $('exMask').classList.add('on');
  $('exDownload').onclick=function(){saveTextFile(fname,text,/\.md$/i.test(fname)?'text/plain':'application/json');};
}
$('exClose').onclick=function(){$('exMask').classList.remove('on');};
$('exCopy').onclick=function(){copyText($('exText').value);};
$('exSelect').onclick=function(){$('exText').select();};
/* ===== v2.15.0 ZIP 打包导出（母题/识题） ===== */
var MT_CRC_TABLE=(function(){var t=[],c,n,k;for(n=0;n<256;n++){c=n;for(k=0;k<8;k++)c=c&1?(c>>>1)^0xEDB88320:c>>>1;t[n]=c>>>0;}return t;})();
function mtCrc32(b){var c=0xFFFFFFFF;for(var i=0;i<b.length;i++)c=(c>>>8)^MT_CRC_TABLE[(c^b[i])&0xFF];return (c^0xFFFFFFFF)>>>0;}
function mtUtf8Enc(s){var b=[];for(var i=0;i<s.length;i++){var c=s.charCodeAt(i);if(c<128)b.push(c);else if(c<2048)b.push(192|c>>6,128|c&63);else if(c<55296||c>=57344)b.push(224|c>>12,128|c>>6&63,128|c&63);else{i++;var c2=s.charCodeAt(i);var cp=65536+((c&1023)<<10)+(c2&1023);b.push(240|cp>>18,128|cp>>12&63,128|cp>>6&63,128|cp&63);}}return new Uint8Array(b);}
function mtZipWrite(files){
  function u16(n){return [n&255,(n>>8)&255];}function u32(n){return [n&255,(n>>8)&255,(n>>16)&255,(n>>>24)&255];}
  var parts=[],central=[],offset=0;
  files.forEach(function(f){
    var name=mtUtf8Enc(f.name),data=f.data,crc=mtCrc32(data),sz=data.length;
    var lh=new Uint8Array([].concat(u32(0x04034b50),u16(20),u16(0x0800),u16(0),u16(0),u16(0),u32(crc),u32(sz),u32(sz),u16(name.length),u16(0)));
    parts.push(lh,name,data);
    var ch=new Uint8Array([].concat(u32(0x02014b50),u16(20),u16(20),u16(0x0800),u16(0),u16(0),u16(0),u32(crc),u32(sz),u32(sz),u16(name.length),u16(0),u16(0),u16(0),u16(0),u32(0),u32(offset)));
    central.push(ch,name);
    offset+=lh.length+name.length+sz;
  });
  var cdSize=central.reduce(function(a,x){return a+x.length;},0);
  var eocd=new Uint8Array([].concat(u32(0x06054b50),u16(0),u16(0),u16(files.length),u16(files.length),u32(cdSize),u32(offset),u16(0)));
  var all=parts.concat(central,[eocd]),total=all.reduce(function(a,x){return a+x.length;},0),out=new Uint8Array(total),p=0;
  all.forEach(function(x){out.set(x,p);p+=x.length;});
  return out;
}
function mtExtractImages(text,state){
  state=state||{seen:{},idx:0,imgs:[]};
  var out=String(text).replace(/data:image\/(png|jpeg|jpg|gif|webp);base64,([A-Za-z0-9+/=]+)/g,function(m,ext,b64){
    if(state.seen[b64])return 'images/'+state.seen[b64];
    state.idx++;var name='img'+state.idx+'.'+(ext==='jpeg'?'jpg':ext);state.seen[b64]=name;
    var bin=atob(b64),arr=new Uint8Array(bin.length);for(var i=0;i<bin.length;i++)arr[i]=bin.charCodeAt(i);
    state.imgs.push({name:'images/'+name,data:arr});
    return 'images/'+name;
  });
  return {text:out,images:state.imgs,state:state};
}
function mtBytesB64(bytes){var bin='',CH=8192;for(var i=0;i<bytes.length;i+=CH)bin+=String.fromCharCode.apply(null,bytes.subarray(i,i+CH));return btoa(bin);}
function saveZipFile(name,bytes){
  if(window.Android&&window.Android.saveFile){try{window.Android.saveFile(name,mtBytesB64(bytes));toast('已保存到手机「下载」：'+name);return;}catch(e){}}
  try{var blob=new Blob([bytes],{type:'application/zip'});var a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=name;document.body.appendChild(a);a.click();a.remove();toast('已触发下载：'+name);}catch(e){toast('下载不可用');}
}
window.mtZipWrite=mtZipWrite;window.mtExtractImages=mtExtractImages;
$('btnExportLibZip').onclick=function(){
  var r=mtExtractImages(eng.exportMotifs());
  var files=[{name:'母题库.json',data:mtUtf8Enc(r.text)}].concat(r.images);
  files.push({name:'说明.txt',data:mtUtf8Enc('母题库ZIP包：母题库.json + images/ 图片。\n导入：APP「录入→JSON导入→或选择ZIP」直接选本zip，图片自动内嵌。\n共'+eng.motifs.length+'条母题，'+r.images.length+'张图片。')});
  saveZipFile('母题库打包.zip',mtZipWrite(files));
};
$('btnExportResultZip').onclick=function(){
  var parts=[];rowsData.forEach(function(row){if((row.stem||'').trim())parts.push((row.no||'')+(row.sub?('('+row.sub+')'):'')+'. '+row.stem);});
  var st={seen:{},idx:0,imgs:[]};
  var r=mtExtractImages(parts.join('\n\n'),st);
  var rr=mtExtractImages(buildResultMd($('resultMode').value),st);
  var files=[{name:'试卷.md',data:mtUtf8Enc(r.text)},{name:'识别结果.md',data:mtUtf8Enc(rr.text)}].concat(st.imgs);
  files.push({name:'说明.txt',data:mtUtf8Enc('识题ZIP包：试卷.md（题目）+ 识别结果.md + images/。\n导入：APP「识题页→图片与压缩包工具→上传ZIP」选本zip。\n共'+rowsData.length+'行。')});
  saveZipFile('识题打包.zip',mtZipWrite(files));
};
$('btnExportLib').onclick=function(){openExport('导出题库 JSON',eng.exportMotifs(),'母题库.json');};
$('btnExportLearn').onclick=function(){openExport('导出学习数据',eng.exportLearning(),'母题学习数据.json');};
$('btnExportAll').onclick=function(){openExport('全量备份',eng.exportData(),'母题全量备份.json');};
$('btnImportLib').onclick=function(){$('libFile').click();};
$('btnImportLearn').onclick=function(){$('learnFile').click();};
$('btnImportAll').onclick=function(){$('allFile').click();};
$('libFile').onchange=function(){var f=this.files[0];if(!f)return;readFile(f,function(t){
  try{var r=eng.importMotifs(JSON.parse(t));toast('题库导入：新增 '+r.added+'，跳过 '+r.skipped);renderBank();renderMe();}catch(e){toast('导入失败：'+e.message);}});this.value='';};
$('learnFile').onchange=function(){var f=this.files[0];if(!f)return;readFile(f,function(t){
  try{var r=eng.importLearning(t);toast('学习数据已导入，样本 '+r.samples+' 条');renderMe();renderBank();}catch(e){toast('导入失败：'+e.message);}});this.value='';};
$('allFile').onchange=function(){var f=this.files[0];if(!f)return;readFile(f,function(t){
  try{eng.importData(t);toast('全量恢复完成');renderMe();renderBank();}catch(e){toast('导入失败：'+e.message);}});this.value='';};
$('btnResetLearn').onclick=function(){
  if(confirm('确定清空全部学习样本、缓存与映射？母题库保留，题库例题会重新自举。')){eng.resetLearning();toast('已清空');renderMe();renderBank();}
};
$('threshold').oninput=function(){$('thVal').textContent=Number(this.value).toFixed(2);};
$('btnSaveSet').onclick=function(){
  eng.settings.apiKey=MT.cleanKey($('apiKey').value);$('apiKey').value=eng.settings.apiKey;
  eng.settings.model=$('model').value;
  eng.settings.localThreshold=parseFloat($('threshold').value);
  eng.settings.priceIn=parseFloat($('priceIn').value)||2;
  eng.settings.priceOut=parseFloat($('priceOut').value)||8;
  eng.settings.priceHit=parseFloat($('priceHit').value)||0.04;
  eng.settings.autoSolution=$('autoSolution').checked;
  eng.settings.deepThinking=$('deepThinking').checked;
  eng.settings.autoTrain=$('autoTrain').checked;
  eng.settings.batchSingles=$('batchSingles').checked;
  eng.saveSettings();toast('设置已保存');renderMe();
};

function updateBridgeTok(){if($('bridgeTokCount'))$('bridgeTokCount').textContent=MT.countTokens($('bridgeText').value);}
$('bridgeText').oninput=updateBridgeTok;
$('btnTkCalc').onclick=function(){$('tkCalcOut').textContent=MT.countTokens($('tkCalc').value)+' tokens（官方分词器离线计算）';};
$('btnFillPrice').onclick=function(){
  var m=$('model').value;
  var p=(m==='deepseek-v4-pro')?[9,27,0.3]:[2,8,0.04];
  $('priceIn').value=p[0];$('priceOut').value=p[1];$('priceHit').value=p[2];
  toast('已填入官方高峰价，保存后生效');
};
$('btnClearMotifs').onclick=function(){
  if(confirm('确定删除全部 '+eng.motifs.length+' 条母题？学习样本与缓存一并清空。可先用「导出题库 JSON」备份。')){
    eng.clearMotifs();renderBank();renderMe();renderRows();toast('题库已清空，可导入 JSON');
  }
};
$('btnTestKey').onclick=function(){
  var key=MT.cleanKey($('apiKey').value);
  if(!key){toast('请先填入 API Key');return;}
  $('testKeyOut').textContent='测试中…（消耗约10 token）';
  window.fetch('https://api.deepseek.com/chat/completions',{method:'POST',headers:{'Content-Type':'application/json','Authorization':'Bearer '+key},body:JSON.stringify({model:$('model').value,messages:[{role:'user',content:'你好'}],max_tokens:1,stream:false,thinking:{type:eng.settings.deepThinking?'enabled':'disabled'}})})
  .then(function(r){if(!r.ok)throw new Error('HTTP '+r.status);return r.json();})
  .then(function(){$('testKeyOut').textContent='✓ 连接成功，Key 有效';})
  .catch(function(e){$('testKeyOut').textContent='✗ 失败：'+e.message+'。401=Key无效（确认来自 platform.deepseek.com、复制完整无空格、未删除）；402=余额不足需充值。';});
};
function fillSynText(){
  var gs=eng.getSynonyms();
  $('synText').value=gs.map(function(g){return g.join('，');}).join('\n');
  $('synCount').textContent='当前 '+gs.length+' 组同义词';
}
document.querySelector('#intakeTabs .sub-tab[data-pane="syn"]').addEventListener('click',fillSynText);
$('btnSynSave').onclick=function(){
  var groups=$('synText').value.split('\n').map(function(l){return l.split(/[,，、]/).map(function(s){return s.trim();}).filter(Boolean);}).filter(function(g){return g.length>=2;});
  var n=eng.setSynonyms(groups);toast('已保存 '+n+' 组同义词，重新学习完成');fillSynText();
};
$('btnSynExport').onclick=function(){openExport('导出同义词库',eng.exportSynonyms(),'同义词库.json');};
$('btnSynImport').onclick=function(){$('synFile').click();};
$('synFile').onchange=function(){var f=this.files[0];if(!f)return;readFile(f,function(t){
  try{var n=eng.importSynonyms(t);toast('已导入 '+n+' 组同义词');fillSynText();}catch(e){toast('导入失败：'+e.message);}});this.value='';};
$('btnSynReset').onclick=function(){var n=eng.resetSynonyms();toast('已恢复内置 '+n+' 组');fillSynText();};
var COURSEWARE_PROMPT='你是高中母题题库构建助手。把我给你的课件文本转成母题JSON数组，要求：\n1. 原子化：一条母题对应一个独立解题模型/一个大招，不建复合母题；综合题靠多母题叠加。\n2. 课件里每个考点/题型都要有对应母题，不遗漏。\n3. 每条母题字段：name(题型名), subject(数学/物理/化学), chapter(讲次), difficulty(简单/中档/较难), sampleQuestion(课件例题题干，保留LaTeX), triggers(识别特征：关键词或同义关键词数组，含术语等价写法如△/三角形、sin/正弦), rules(识别判据：命中即判定的结构特征数组), solution(解法步骤数组), keyPoints(关键点数组), moveName(大招名称，无则填"无"), move(大招口诀+用法，无则空), caveat(易错点数组), modelIdentify(模型识别描述), highFrequencyFormula(高频公式数组；没有大招时必填基础公式)。\n4. triggers要用关键词/同义关键词，便于语义匹配；rules要准确可判定。\n5. 有大招/模板就写moveName和move；没有就moveName填"无"，把基础公式写进highFrequencyFormula。\n6. 只输出JSON数组，不要输出其他内容。\n\n课件文本如下：\n';
$('btnCopyCourseware').onclick=function(){copyText(COURSEWARE_PROMPT);};
function refreshCatalogSubjects(){
  var sel=$('catalogSubjectSel');if(!sel)return;
  var set={};eng.motifs.forEach(function(m){set[m.subject||'其他']=1;});
  var order=['数学','物理','化学','生物','政治','历史','地理','英语','语文'];
  var ss=Object.keys(set).sort(function(a,b){var ia=order.indexOf(a),ib=order.indexOf(b);return (ia<0?99:ia)-(ib<0?99:ib);});
  var cur=eng.settings.catalogSubject||'all';
  if(cur!=='all'&&ss.indexOf(cur)<0)cur='all';
  sel.innerHTML='<option value="all">全部学科目录</option>'+ss.map(function(s){return '<option value="'+esc(s)+'">'+esc(s)+'目录</option>';}).join('');
  sel.value=cur;
  sel.disabled=!eng.settings.catalogInPrompt;
}
function renderRecMode(){
  var m=eng.settings.recMode||'hybrid';
  document.querySelectorAll('#recModeBar [data-mode]').forEach(function(b){b.classList.toggle('pri',b.dataset.mode===m);});
  var hints={hybrid:'共同参与（默认最省）：学过的题缓存直出，本地有把握直接判，没把握才请DeepSeek细分题型特征（目录可选）再由本地配母题。',ai:'AI识别：DeepSeek直接判定题型名称（覆盖数理化，目录可选），本地按名匹配母题，最直接。',offline:'离线识别：只用本地神经网络，绝不联网，0 token；判不出的题给候选，人工勾选即学会。'};
  $('recModeHint').textContent=hints[m]||hints.hybrid;
  if(m==='offline'&&!eng.settings.autoTrain)$('recModeHint').textContent+='（训练开关已关，本地判定不可用）';
  if($('catalogToggle'))$('catalogToggle').checked=!!eng.settings.catalogInPrompt;
  if($('catalogStrategySel'))$('catalogStrategySel').value=eng.settings.catalogStrategy||(eng.settings.catalogInPrompt?'full':'ondemand');
  refreshCatalogSubjects();
}
document.querySelectorAll('#recModeBar [data-mode]').forEach(function(b){b.onclick=function(){eng.settings.recMode=b.dataset.mode;eng.saveSettings();renderRecMode();updateBatchEstimate();};});
$('autoTrain').onchange=function(){eng.settings.autoTrain=this.checked;eng.saveSettings();if(this.checked){eng.trainNow();toast('已开启本地训练，后台学习中…');}else{toast('已关闭本地训练：不训练/不准备/不加载权重');}renderRecMode();};
$('catalogToggle').onchange=function(){eng.settings.catalogInPrompt=this.checked;eng.settings.catalogStrategy=this.checked?'full':'ondemand';eng.settings.catalogFamily=true;if($('catalogStrategySel'))$('catalogStrategySel').value=eng.settings.catalogStrategy;eng.cache={};eng.saveSettings();refreshCatalogSubjects();renderRows();updateBatchEstimate();toast(this.checked?'已开启目录进提示词（本地缓存已清，重新识别更准）':'已关闭目录进提示词（本地缓存已清）');};
$('catalogStrategySel').onchange=function(){var v=this.value;eng.settings.catalogStrategy=v;eng.settings.catalogInPrompt=(v==='full');eng.settings.catalogFamily=(v!=='off');if($('catalogToggle'))$('catalogToggle').checked=(v==='full');eng.cache={};eng.saveSettings();refreshCatalogSubjects();renderRows();updateBatchEstimate();toast('目录策略：'+(v==='full'?'全量':v==='ondemand'?'按需':'关闭')+'（本地缓存已清）');};
$('catalogSubjectSel').onchange=function(){eng.settings.catalogSubject=this.value;eng.cache={};eng.saveSettings();updateBatchEstimate();toast('目录学科已切换为'+(this.value==='all'?'全部学科':this.value)+'（本地缓存已清）');};
document.querySelectorAll('#matchSummary .stat').forEach(function(s){s.onclick=function(){rowFilter=(rowFilter===s.dataset.filter&&s.dataset.filter!=='all')?'all':s.dataset.filter;renderRows();};});
var solQ='',solIds=[],solRowIdx=-1;
function solutionHTML(m){
  var kp=Array.isArray(m.keyPoints)?m.keyPoints:(m.keyPoints?[m.keyPoints]:[]);
  var h='<div class="sol-motif"><div class="mname">'+esc(m.name)+'</div><div class="meta">'+esc(m.chapter||'')+' · '+esc(m.difficulty||'')+'</div>';
  if(m.moveName&&m.moveName!=='无'&&m.move)h+='<div class="movebox"><div class="mn">'+esc(m.moveName)+'</div><div class="mc">'+mx(m.move)+'</div></div>';
  if(m.solution&&m.solution.length)h+='<div class="sec"><div class="sec-t">解法步骤</div><ol class="steps">'+m.solution.map(function(s,j){return '<li><span class="num">'+(j+1)+'</span><p>'+mx(s)+'</p></li>';}).join('')+'</ol></div>';
  if(kp.length)h+='<div class="sec"><div class="sec-t">关键点</div><div class="note">'+kp.map(mx).join('<br>')+'</div></div>';
  if(m.highFrequencyFormula&&m.highFrequencyFormula.length)h+='<div class="sec"><div class="sec-t">高频公式</div>'+m.highFrequencyFormula.map(function(f){return '<div class="fx" style="margin-bottom:6px">'+mx(f)+'</div>';}).join('')+'</div>';
  if(m.caveat&&m.caveat.length)h+='<div class="sec"><div class="sec-t">易错警示</div><div class="note warn">'+m.caveat.map(mx).join('<br>')+'</div></div>';
  return h+'</div>';
}
function openSolution(ids,q,rowIdx){
  solQ=q||'';solIds=ids||[];solRowIdx=(rowIdx===undefined?-1:rowIdx);
  var h='';solIds.forEach(function(i){if(eng.motifs[i])h+=solutionHTML(eng.motifs[i]);});
  $('solBody').innerHTML=h||'<div class="empty">无匹配母题</div>';
  $('solTitle').textContent='解法 · '+solIds.map(function(i){return eng.motifs[i]?eng.motifs[i].name:'';}).join(' + ');
  var ai=(solRowIdx>=0&&rowsData[solRowIdx]&&rowsData[solRowIdx].aiSolution)?rowsData[solRowIdx].aiSolution:null;
  $('solAiOut').innerHTML=ai?'<div class="note">'+mx(ai.text).replace(/\n/g,'<br>')+'</div><p class="hint">'+ai.tokens+' token · 约¥'+ai.costEst.toFixed(4)+' · 已保存</p>':'';
  $('solPanel').classList.add('on');$('solBackdrop').classList.add('on');document.body.classList.add('sol-open');
}
function aiSolveRow(idx){
  var row=rowsData[idx];
  if(!eng.settings.apiKey){toast('先在设置填入 API Key');return;}
  var stem=(row.stem||'').trim();if(!stem){toast('题干为空');return;}
  if(row.aiSolution&&!confirm('已有AI详解，重新生成会再耗token，继续？'))return;
  row.aiLoading=true;renderRows();
  var motifs=(row.result&&row.result.ids||[]).map(function(i){return eng.motifs[i];}).filter(Boolean);
  eng.aiSolve(stem,motifs).then(function(r){
    row.aiSolution={text:r.text,tokens:r.tokens,costEst:r.costEst,ts:Date.now()};row.aiLoading=false;saveRows();renderRows();renderMe();toast('AI详解已生成并保存');
  }).catch(function(e){row.aiLoading=false;renderRows();toast('AI详解失败：'+(e.message||e));});
}
function closeSolution(){$('solPanel').classList.remove('on');$('solBackdrop').classList.remove('on');document.body.classList.remove('sol-open');}
$('solClose').onclick=closeSolution;
$('solBackdrop').onclick=closeSolution;
$('btnSolAi').onclick=function(){
  if(!eng.settings.apiKey){toast('先在设置填入 API Key');return;}
  if(!solQ){toast('无题目可详解');return;}
  if(solRowIdx>=0&&rowsData[solRowIdx]&&rowsData[solRowIdx].aiSolution&&!confirm('已有详解，重新生成会再耗token，继续？'))return;
  $('solAiOut').innerHTML='<div class="empty">AI详解生成中…（耗token）</div>';
  eng.aiSolve(solQ,solIds.map(function(i){return eng.motifs[i];}).filter(Boolean)).then(function(r){
    $('solAiOut').innerHTML='<div class="note">'+mx(r.text).replace(/\n/g,'<br>')+'</div><p class="hint">本次 '+r.tokens+' token · 约¥'+r.costEst.toFixed(4)+' · 已保存</p>';
    if(solRowIdx>=0&&rowsData[solRowIdx]){rowsData[solRowIdx].aiSolution={text:r.text,tokens:r.tokens,costEst:r.costEst,ts:Date.now()};saveRows();renderRows();}
    renderMe();
  }).catch(function(e){$('solAiOut').innerHTML='<div class="notice a">'+esc(e.message||e)+'</div>';});
};
/* ---- 试卷库 ---- */
function loadPapers(){try{return JSON.parse(window.localStorage.getItem('mt.papers')||'[]');}catch(e){return[];}}
function savePapersArr(p){try{window.localStorage.setItem('mt.papers',JSON.stringify(p));}catch(e){}}
$('btnSavePaper').onclick=function(){
  if(!rowsData.length){toast('没有题目可存');return;}
  var title=prompt('试卷名称：','试卷_'+new Date().toLocaleDateString());
  if(title===null)return;
  var papers=loadPapers();
  var rowsCopy=JSON.parse(JSON.stringify(rowsData));
  var hit=0;rowsCopy.forEach(function(r){r.motifNames=(r.result&&r.result.ids||[]).map(function(id){return eng.motifs[id]?eng.motifs[id].name:'?';});if(r.motifNames.length)hit++;});
  papers.push({id:Date.now(),title:title||'未命名试卷',createdAt:new Date().toISOString(),count:rowsCopy.length,hit:hit,rows:rowsCopy});
  savePapersArr(papers);toast('已存入试卷库');renderPapers();
};
function rowMotifIds(r){
  var names=r.motifNames||(r.result&&r.result.names)||[];
  var ids=[];
  names.forEach(function(n){for(var i=0;i<eng.motifs.length;i++){if(eng.motifs[i].name===n){ids.push(i);break;}}});
  if(!ids.length&&r.result&&r.result.ids){r.result.ids.forEach(function(i){if(eng.motifs[i]&&ids.indexOf(i)<0)ids.push(i);});}
  return ids;
}
var DIFF_W={'基础':1,'简单':1,'中档':2,'难题':3,'较难':3};
var DIFF_L={1:'基础',2:'中档',3:'难题'};
function rowDiff(r){
  var best=0;
  rowMotifIds(r).forEach(function(i){var w=DIFF_W[eng.motifs[i].difficulty]||2;if(w>best)best=w;});
  return best;
}
function paperDiffStats(p){
  var c={1:0,2:0,3:0},sum=0,n=0;
  (p.rows||[]).forEach(function(r){var d=rowDiff(r);if(d){c[d]++;sum+=d;n++;}});
  return {c:c,n:n,avg:n?sum/n:0,label:n?(sum/n<1.5?'基础':sum/n<2.4?'中档':'难题'):'未识别'};
}
function renderPapers(){
  var papers=loadPapers();
  var kw=($('paperSearch').value||'').trim().toLowerCase();
  var filtered=[];
  papers.forEach(function(p,i){
    if(!kw){filtered.push({p:p,i:i});return;}
    var hit=(p.title||'').toLowerCase().indexOf(kw)>=0;
    if(!hit){hit=(p.rows||[]).some(function(r){return (r.stem||'').toLowerCase().indexOf(kw)>=0||(r.motifNames||[]).some(function(n){return String(n).toLowerCase().indexOf(kw)>=0;});});}
    if(hit)filtered.push({p:p,i:i});
  });
  $('papersCount').textContent=papers.length+' 份'+(kw?' · 匹配'+filtered.length:'');
  var cps=$('cpSource');if(cps){var cv=cps.value;cps.innerHTML='<option value="-1">全部试卷（'+papers.length+'份）</option>'+papers.map(function(p,i){return '<option value="'+i+'">'+esc(p.title)+'</option>';}).join('');if(cv&&cps.querySelector('option[value="'+cv+'"]'))cps.value=cv;}
  renderCpMotifs();
  $('papersList').innerHTML=filtered.map(function(o){
    var p=o.p,i=o.i;var ds=paperDiffStats(p);
    return '<div class="card"><div class="card-h"><h2>'+esc(p.title)+'</h2><span class="sub">'+p.count+'题 · 命中'+p.hit+' · 难度'+ds.label+(ds.n?'（基'+ds.c[1]+'·中'+ds.c[2]+'·难'+ds.c[3]+'）':'')+' · '+esc((p.createdAt||'').slice(0,10))+'</span></div><div class="card-b actbar"><button class="btn sm" data-paperopen="'+i+'">打开</button><button class="btn sm" data-paperexport="'+i+'">导出</button><button class="btn sm dgr" data-paperdel="'+i+'">删除</button></div></div>';
  }).join('')||'<div class="empty">'+(kw?'没有匹配的试卷':'试卷仓库为空。在「识题」页识别试卷后点「存入试卷库」。')+'</div>';
  document.querySelectorAll('[data-paperopen]').forEach(function(b){b.onclick=function(){openPaper(parseInt(b.dataset.paperopen,10));};});
  document.querySelectorAll('[data-paperexport]').forEach(function(b){b.onclick=function(){var p=loadPapers()[parseInt(b.dataset.paperexport,10)];if(p)saveTextFile((p.title||'试卷')+'.json',JSON.stringify(p,null,1));};});
  document.querySelectorAll('[data-paperdel]').forEach(function(b){b.onclick=function(){var i=parseInt(b.dataset.paperdel,10);var ps=loadPapers();if(confirm('删除试卷「'+(ps[i]?ps[i].title:'')+'」？')){ps.splice(i,1);savePapersArr(ps);renderPapers();}};});
}
$('paperSearch').oninput=function(){renderPapers();};
function openPaper(i){
  var p=loadPapers()[i];if(!p)return;
  var ds=paperDiffStats(p);
  $('paperTitle').textContent=p.title+' · 难度'+ds.label+(ds.n?'（基'+ds.c[1]+'·中'+ds.c[2]+'·难'+ds.c[3]+'）':'');
  $('paperBody').innerHTML=(p.rows||[]).map(function(r,ri){
    var ids=rowMotifIds(r);
    var names=ids.map(function(id){return eng.motifs[id].name;});
    var d=rowDiff(r);
    return '<div class="sol-motif"><div class="mname">'+esc(rowLabel(r))+(r.section?' <span class="mini gray">'+esc(r.section)+'</span>':'')+' <span class="mini'+(d===3?' teal':' gray')+'">'+(d?DIFF_L[d]:'未识别')+'</span></div><div class="stem-render">'+formatStem(r.stem)+'</div><div class="meta">母题：'+esc(names.join(' + ')||'未识别')+(ids.length?' <a href="javascript:void(0)" data-papsol="'+ri+'" style="color:var(--pri)">查看解法 ›</a>':'')+'</div></div>';
  }).join('');
  document.querySelectorAll('#paperBody [data-papsol]').forEach(function(a){a.onclick=function(){
    var r=p.rows[parseInt(a.dataset.papsol,10)];
    openSolution(rowMotifIds(r),r.stem,-1);
  };});
  $('paperMask').classList.add('on');
}
$('paperClose').onclick=function(){$('paperMask').classList.remove('on');};
$('btnImportPaper').onclick=function(){$('paperLibFile').click();};
$('paperLibFile').onchange=function(){var f=this.files[0];if(!f)return;readFile(f,function(t){
  try{var p=JSON.parse(t);if(!p.rows)throw new Error('格式不对');var ps=loadPapers();p.id=Date.now();ps.push(p);savePapersArr(ps);renderPapers();toast('试卷已导入');}catch(e){toast('导入失败：'+e.message);}});this.value='';};
var cpChecked=new Set();
var cpSecs=new Set(),cpDiffs=new Set();
function renderCpChips(){
  var secs=['单选','多选','选择','填空','解答','实验','例题'];
  $('cpSecChips').innerHTML=secs.map(function(s){return '<button class="tagbtn'+(cpSecs.has(s)?' on':'')+'" data-cpsec="'+s+'">'+s+'</button>';}).join('');
  $('cpDiffChips').innerHTML=[['1','基础'],['2','中档'],['3','难题']].map(function(d){return '<button class="tagbtn'+(cpDiffs.has(d[0])?' on':'')+'" data-cpdiff="'+d[0]+'">'+d[1]+'</button>';}).join('');
  document.querySelectorAll('[data-cpsec]').forEach(function(b){b.onclick=function(){var s=b.dataset.cpsec;if(cpSecs.has(s))cpSecs.delete(s);else cpSecs.add(s);renderCpChips();};});
  document.querySelectorAll('[data-cpdiff]').forEach(function(b){b.onclick=function(){var d=b.dataset.cpdiff;if(cpDiffs.has(d))cpDiffs.delete(d);else cpDiffs.add(d);renderCpChips();};});
}
$('cpFoldH').onclick=function(){var b=$('cpBody');var open=b.style.display==='none';b.style.display=open?'':'none';this.classList.toggle('open',open);};
function cpFiltered(){
  var subj=$('cpSubject').value,ch=$('cpChapter').value;
  return eng.motifs.filter(function(m){
    if(subj&&(m.subject||'其他')!==subj)return false;
    if(ch&&(m.chapter||'未分类')!==ch)return false;
    return true;
  });
}
function renderCpMotifList(){
  var list=cpFiltered();
  var cnt={};loadPapers().forEach(function(p){(p.rows||[]).forEach(function(r){rowMotifIds(r).forEach(function(i){cnt[i]=(cnt[i]||0)+1;});});});
  $('cpMotifList').innerHTML=list.map(function(m){
    var i=eng.motifs.indexOf(m);
    return '<label class="ck" style="border:none;padding:3px 0;display:flex;gap:6px;align-items:flex-start"><input type="checkbox" data-cpm="'+esc(m.name)+'"'+(cpChecked.has(m.name)?' checked':'')+' style="width:16px;height:16px;margin-top:3px;accent-color:var(--pri)"><span style="font-size:12.5px">'+esc(m.name)+' <span class="mini gray">'+esc(m.difficulty||'')+'</span> <span class="mini">'+esc(m.chapter||'')+'</span> <span class="mini'+(cnt[i]?' teal':' gray')+'">'+(cnt[i]||0)+'题</span></span></label>';
  }).join('')||'<div class="empty">该科目/讲次下无母题</div>';
  $('cpCheckedCount').textContent='已勾'+cpChecked.size;
  document.querySelectorAll('#cpMotifList [data-cpm]').forEach(function(cb){cb.onchange=function(){if(this.checked)cpChecked.add(this.dataset.cpm);else cpChecked.delete(this.dataset.cpm);$('cpCheckedCount').textContent='已勾'+cpChecked.size;};});
}
function renderCpMotifs(){
  var subjects={};eng.motifs.forEach(function(m){subjects[m.subject||'其他']=1;});
  var ssel=$('cpSubject'),sv=ssel.value;
  ssel.innerHTML='<option value="">全部科目</option>'+Object.keys(subjects).map(function(s){return '<option value="'+esc(s)+'">'+esc(s)+'</option>';}).join('');
  if(sv&&ssel.querySelector('option[value="'+sv+'"]'))ssel.value=sv;
  var chs={};cpFiltered().forEach(function(m){chs[m.chapter||'未分类']=1;});
  var csel=$('cpChapter'),cv=csel.value;
  csel.innerHTML='<option value="">全部讲次</option>'+Object.keys(chs).map(function(c){return '<option value="'+esc(c)+'">'+esc(c)+'</option>';}).join('');
  if(cv&&csel.querySelector('option[value="'+cv+'"]'))csel.value=cv;
  renderCpMotifList();
}
$('cpSubject').onchange=function(){renderCpMotifs();};
$('cpChapter').onchange=function(){renderCpMotifList();};
$('cpSelAll').onclick=function(){cpFiltered().forEach(function(m){cpChecked.add(m.name);});renderCpMotifList();};
$('cpSelNone').onclick=function(){cpChecked.clear();renderCpMotifList();};
$('btnCompose').onclick=function(){
  var papers=loadPapers();
  if(!papers.length){toast('试卷库为空，先导入并识别试卷');return;}
  var subj=$('cpSubject').value;
  var src=parseInt($('cpSource').value,10);
  var n=Math.max(1,Math.min(100,parseInt($('cpCount').value,10)||10));
  var pool=[],seen={};
  papers.forEach(function(p,pi){
    if(src>=0&&pi!==src)return;
    (p.rows||[]).forEach(function(r){
      if(!(r.stem||'').trim())return;
      if(cpSecs.size&&!cpSecs.has(r.section||''))return;
      if(cpDiffs.size&&!cpDiffs.has(String(rowDiff(r))))return;
      var ids=rowMotifIds(r);
      if(subj){var s=ids.length?(eng.motifs[ids[0]].subject||'其他'):'';if(s!==subj)return;}
      if(cpChecked.size){
        var hit=false;
        for(var i=0;i<ids.length;i++){if(cpChecked.has(eng.motifs[ids[i]].name)){hit=true;break;}}
        if(!hit)return;
      }
      var k=MT.cacheKey(r.stem);if(seen[k])return;seen[k]=1;
      pool.push(r);
    });
  });
  if(!pool.length){toast('没有符合条件的题：换母题知识点或放宽筛选');return;}
  for(var i=pool.length-1;i>0;i--){var j=Math.floor(Math.random()*(i+1));var t=pool[i];pool[i]=pool[j];pool[j]=t;}
  var rows=pool.slice(0,n).map(function(r,i){
    var c=JSON.parse(JSON.stringify(r));c.no=i+1;c.sub=0;c.sub2='';c.error='';
    var ids=rowMotifIds(c);c.motifNames=ids.map(function(id){return eng.motifs[id].name;});
    return c;
  });
  var hit=rows.filter(function(r){return r.motifNames&&r.motifNames.length;}).length;
  var title='组卷_'+(subj||'综合')+'_'+new Date().toLocaleDateString()+'_'+rows.length+'题';
  var ps=loadPapers();ps.push({id:Date.now(),title:title,createdAt:new Date().toISOString(),count:rows.length,hit:hit,rows:rows,source:'组卷'});
  savePapersArr(ps);renderPapers();toast('组卷完成：'+rows.length+'题（候选'+pool.length+'）');openPaper(ps.length-1);
};
/* ---- 视图切换 ---- */
function switchView(v){
  document.querySelectorAll('.navi[data-view]').forEach(function(x){x.classList.toggle('on',x.dataset.view===v);});
  document.querySelectorAll('.view').forEach(function(x){x.classList.remove('on');});
  $('view-'+v).classList.add('on');
  if(v==='me')renderMe();
  if(v==='bank')renderBank();
  if(v==='solver')renderRows();
  if(v==='papers')renderPapers();
}
document.querySelectorAll('.navi[data-view]').forEach(function(b){
  b.onclick=function(){switchView(b.dataset.view);};
});

/* ===== v2.10.0 三天试用 + 激活码 ===== */
/*LIC-START*/
var TRIAL_DAYS=3,TRIAL_HARD_END='2026-12-03';
var TRIAL_SECRET=String.fromCharCode(77,84,45,76,73,67,45,50,48,50,54,45,57,102,51,97,55,99,49,101,53,98,56,100,52,50,54,48,45,97,55,101,50);
var TRIAL_SECRET_V1=String.fromCharCode(72,69,74,73,69,45,77,84,45,50,48,50,54,45,88,55,75,57);
function _utf8(s){var b=[];for(var i=0;i<s.length;i++){var c=s.charCodeAt(i);if(c<128)b.push(c);else if(c<2048){b.push(192|c>>6,128|c&63);}else if(c<55296||c>=57344){b.push(224|c>>12,128|c>>6&63,128|c&63);}else{i++;var c2=s.charCodeAt(i);var cp=65536+((c&1023)<<10)+(c2&1023);b.push(240|cp>>18,128|cp>>12&63,128|cp>>6&63,128|cp&63);}}return b;}
function sha256Bytes(msg){
  var K=[0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2];
  var H=[0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19];
  var l=msg.length;var withOne=l+1;var padLen=(withOne%64<=56)?(56-withOne%64):(120-withOne%64);
  var m=msg.slice();m.push(0x80);for(var i=0;i<padLen;i++)m.push(0);
  var bitHi=Math.floor(l/536870912),bitLo=(l<<3)>>>0;m.push((bitHi>>>24)&255,(bitHi>>>16)&255,(bitHi>>>8)&255,bitHi&255,(bitLo>>>24)&255,(bitLo>>>16)&255,(bitLo>>>8)&255,bitLo&255);
  var w=new Array(64);
  function rr(x,n){return (x>>>n)|(x<<(32-n));}
  for(var off=0;off<m.length;off+=64){
    for(var t=0;t<16;t++)w[t]=(m[off+t*4]<<24)|(m[off+t*4+1]<<16)|(m[off+t*4+2]<<8)|m[off+t*4+3];
    for(t=16;t<64;t++){var s0=rr(w[t-15],7)^rr(w[t-15],18)^(w[t-15]>>>3);var s1=rr(w[t-2],17)^rr(w[t-2],19)^(w[t-2]>>>10);w[t]=(w[t-16]+s0+w[t-7]+s1)|0;}
    var a=H[0],b=H[1],c=H[2],d=H[3],e=H[4],f=H[5],g=H[6],h=H[7];
    for(t=0;t<64;t++){var S1=rr(e,6)^rr(e,11)^rr(e,25);var ch=(e&f)^(~e&g);var t1=(h+S1+ch+K[t]+w[t])|0;var S0=rr(a,2)^rr(a,13)^rr(a,22);var maj=(a&b)^(a&c)^(b&c);var t2=(S0+maj)|0;h=g;g=f;f=e;e=(d+t1)|0;d=c;c=b;b=a;a=(t1+t2)|0;}
    H[0]=(H[0]+a)|0;H[1]=(H[1]+b)|0;H[2]=(H[2]+c)|0;H[3]=(H[3]+d)|0;H[4]=(H[4]+e)|0;H[5]=(H[5]+f)|0;H[6]=(H[6]+g)|0;H[7]=(H[7]+h)|0;
  }
  var out=[];for(var i2=0;i2<8;i2++)out.push((H[i2]>>>24)&255,(H[i2]>>>16)&255,(H[i2]>>>8)&255,H[i2]&255);
  return out;
}
function sha256Hex(bytes){var s='';for(var i=0;i<bytes.length;i++){var h=bytes[i].toString(16);if(h.length<2)h='0'+h;s+=h;}return s;}
function hmacSha256(keyStr,msgStr){
  var k=_utf8(keyStr);if(k.length>64)k=sha256Bytes(k);while(k.length<64)k.push(0);
  var ipad=[],opad=[];for(var i=0;i<64;i++){ipad.push(k[i]^0x36);opad.push(k[i]^0x5c);}
  var inner=sha256Bytes(ipad.concat(_utf8(msgStr)));
  return sha256Hex(sha256Bytes(opad.concat(inner)));
}

function tLoad(k,d){try{var v=window.localStorage.getItem(k);return v?JSON.parse(v):d;}catch(e){return d;}}
function tSave(k,v){try{window.localStorage.setItem(k,JSON.stringify(v));}catch(e){}}
function trialHash(str){var h1=0xdeadbeef,h2=0x41c6ce57;for(var i=0,ch;i<str.length;i++){ch=str.charCodeAt(i);h1=Math.imul(h1^ch,2654435761);h2=Math.imul(h2^ch,1597334677);}h1=Math.imul(h1^(h1>>>16),2246822507)^Math.imul(h2^(h2>>>13),3266489909);h2=Math.imul(h2^(h2>>>16),2246822507)^Math.imul(h1^(h1>>>13),3266489909);return ((h2>>>0).toString(36)+(h1>>>0).toString(36)).toUpperCase();}
function trialDevId(){
  try{if(window.Android&&typeof window.Android.getDeviceId==='function'){var hw=String(window.Android.getDeviceId()||'');if(hw.length>=8&&hw!=='9774d56d682e549c')return trialHash('HW|'+hw).replace(/[^A-Z0-9]/g,'').slice(0,6);}}catch(e){}
  var id=tLoad('mt.devId',null);if(!id){id=(Date.now().toString(36)+Math.random().toString(36).slice(2,8)).toUpperCase().replace(/[^A-Z0-9]/g,'').slice(-6);tSave('mt.devId',id);}return id;}
function trialCode(devId){var h=hmacSha256(TRIAL_SECRET,'MT-LIC-v2|'+String(devId).toUpperCase().trim()).toUpperCase();return h.slice(0,4)+'-'+h.slice(4,8)+'-'+h.slice(8,12)+'-'+h.slice(12,16);}
function trialCodeLegacy(devId){var s=trialHash(String(devId).toUpperCase().trim()+'|'+TRIAL_SECRET_V1).replace(/[^A-Z0-9]/g,'');while(s.length<8)s+='0';return s.slice(0,4)+'-'+s.slice(4,8);}
var LIC_EPOCH=Date.UTC(2020,0,1),PLAN_DAYS={M1:30,M3:90,PM:0};
function trialCodeV3(devId,plan,issueDay){var d36=issueDay.toString(36).toUpperCase();while(d36.length<4)d36='0'+d36;var payload=plan+d36;var mac=hmacSha256(TRIAL_SECRET,'MT-LIC-v3|'+String(devId).toUpperCase().trim()+'|'+payload).toUpperCase().replace(/[^A-F0-9]/g,'');var s=(payload+mac).slice(0,16);return s.slice(0,4)+'-'+s.slice(4,8)+'-'+s.slice(8,12)+'-'+s.slice(12,16);}
/*LIC-END*/
function trialNow(){var now=Date.now(),last=tLoad('mt.trialLast',0);if(now<last)return last;tSave('mt.trialLast',now);return now;}
function trialMarkerRead(){try{if(window.AndroidTrial&&typeof window.AndroidTrial.readMarker==='function'){var n=parseInt(String(window.AndroidTrial.readMarker()||''),10);if(n>1600000000000&&n<9999999999999)return n;}}catch(e){}return null;}
function trialMarkerWrite(ts){try{if(window.AndroidTrial&&typeof window.AndroidTrial.writeMarker==='function')window.AndroidTrial.writeMarker(trialDevId(),String(ts));}catch(e){}}
function trialStartTs(){var mk=trialMarkerRead();var st=tLoad('mt.trialStart',null);if(mk!==null&&(!st||mk<st)){st=mk;tSave('mt.trialStart',st);}if(!st){st=trialNow();tSave('mt.trialStart',st);}if(mk===null)trialMarkerWrite(st);return st;}
function licInfo(){var l=tLoad('mt.lic',null);if(!l)return null;if(typeof l==='string')return {plan:'PM'};return l;}
function licExpired(){var l=licInfo();if(!l||l.plan==='PM')return false;return trialNow()>(l.end||0);}
function trialExpired(){if(licInfo()&&!licExpired())return false;var now=trialNow();if(now>new Date(TRIAL_HARD_END+'T23:59:59').getTime())return true;return now-trialStartTs()>TRIAL_DAYS*86400000;}
function renderTrialInfo(){var l=licInfo();var el=$('meTrialLeft');var txt;
  if(l&&!licExpired()){txt=l.plan==='PM'?'正式版（永久）':'正式版 · 剩余 '+Math.max(0,Math.ceil((l.end-trialNow())/86400000))+' 天';}
  else if(l&&licExpired()){txt='授权已到期，请续费';}
  else{var st=trialStartTs();var left=Math.max(0,Math.ceil((Math.min(st+TRIAL_DAYS*86400000,new Date(TRIAL_HARD_END+'T23:59:59').getTime())-trialNow())/86400000));txt=left>0?('试用中 · 剩余 '+left+' 天'):'试用已结束';}
  if(el)el.textContent=txt;if($('meDevId'))$('meDevId').textContent=trialDevId();if($('trialFoldSub'))$('trialFoldSub').textContent=txt;}
function trialCheck(){var el=$('trialLock');if(el){if(trialExpired()){el.style.display='flex';if($('trialDev'))$('trialDev').textContent=trialDevId();if($('trialTitle'))$('trialTitle').textContent=(licInfo()&&licExpired())?'授权已到期，续费请联系作者':TRIAL_DAYS+'天试用已结束';}else el.style.display='none';}renderTrialInfo();}
function tryActivate(inputEl,msgEl){
  var raw=(inputEl.value||'').toUpperCase().replace(/[^A-Z0-9]/g,'');
  var dev=trialDevId(),ok=false,licVal=null,failMsg='激活码不正确，请核对设备码后重试';
  if(raw.length===16){
    var plan=raw.slice(0,2);
    if(PLAN_DAYS.hasOwnProperty(plan)){
      var day=parseInt(raw.slice(2,6),36);
      if(day>=0&&day<1679616&&trialCodeV3(dev,plan,day).replace(/-/g,'')===raw){
        if(plan==='PM'){licVal={plan:'PM'};ok=true;}
        else{var end=LIC_EPOCH+day*86400000+PLAN_DAYS[plan]*86400000;
          if(trialNow()>end){failMsg='该授权已到期，续费请向作者获取新码';}
          else{licVal={plan:plan,end:end};ok=true;}}
      }
    }
    if(!ok&&failMsg==='激活码不正确，请核对设备码后重试'&&raw===trialCode(dev).replace(/-/g,'')){licVal={plan:'PM'};ok=true;}
  }else if(raw.length===8&&raw===trialCodeLegacy(dev).replace('-','')){licVal={plan:'PM'};ok=true;}
  if(ok){tSave('mt.lic',licVal);if(msgEl){msgEl.textContent=licVal.plan==='PM'?'激活成功，已解锁永久正式版！':'激活成功，授权有效期已开启！';msgEl.style.color='#15803d';}toast('激活成功');}
  else if(msgEl){msgEl.textContent=failMsg;msgEl.style.color='#b91c1c';}
  trialCheck();return ok;}
$('btnTrialAct').onclick=function(){tryActivate($('trialCode'),$('trialErr'));};
$('btnMeAct').onclick=function(){tryActivate($('meActCode'),$('meActMsg'));};
var SELLER_QQ='3483917056';
function copyContact(t){if(navigator.clipboard&&navigator.clipboard.writeText){navigator.clipboard.writeText(t).then(function(){toast('已复制：'+t);},function(){prompt('长按复制：',t);});}else{prompt('长按复制：',t);}}
$('trialFoldH').onclick=function(){var b=$('trialCardBody');var open=b.style.display==='none';b.style.display=open?'':'none';this.classList.toggle('open',open);};
$('btnCopyQq').onclick=function(){copyContact(SELLER_QQ);};
$('btnLockQq').onclick=function(){copyContact(SELLER_QQ);};
$('meQq').textContent=SELLER_QQ;$('lockQq').textContent=SELLER_QQ;
function saveQr(){var b64=$('lockQr').src.split(',')[1];if(window.Android&&typeof window.Android.saveImage==='function'){try{window.Android.saveImage('母题APP-作者微信二维码.png',b64);toast('已保存到相册；打开微信→扫一扫→右上角相册→选此二维码');return;}catch(e){}}toast('请长按二维码图片保存到相册，再用微信扫一扫从相册识别');}
$('btnLockQrSave').onclick=saveQr;$('btnMeQrSave').onclick=saveQr;
window.trialCheck=trialCheck;window.trialCode=trialCode;window.trialCodeLegacy=trialCodeLegacy;window.trialCodeV3=trialCodeV3;window.trialExpired=trialExpired;window.trialDevId=trialDevId;

renderBank();renderMe();renderRows();renderRecMode();renderCpMotifs();renderCpChips();
trialCheck();
})();
