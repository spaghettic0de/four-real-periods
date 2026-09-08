import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import boxes from './regions.json';
const canvas=document.querySelector('#scene'),renderer=new THREE.WebGLRenderer({canvas,antialias:true,alpha:true,preserveDrawingBuffer:true});renderer.setPixelRatio(Math.min(devicePixelRatio,2));renderer.setClearColor(0x090f13,0);
const scene=new THREE.Scene(),camera=new THREE.PerspectiveCamera(35,1,.1,100);camera.position.set(4,4.2,7.2);const controls=new OrbitControls(camera,canvas);controls.enableDamping=true;controls.enablePan=false;controls.minDistance=5;controls.maxDistance=14;controls.target.set(.2,.35,0);
const group=new THREE.Group();group.position.y=.65;scene.add(group);
const verts=[new THREE.Vector3(-2,-1,-1.4),new THREE.Vector3(2,-1,-1.4),new THREE.Vector3(0,-1,2),new THREE.Vector3(0,2.3,0)];
function project(r){const v=new THREE.Vector3();r.forEach((a,i)=>v.addScaledVector(verts[i],a*6/5));return v;}
const corners=[[5/6,0,0,0],[5/12,5/12,0,0],[5/18,5/18,5/18,0],[5/24,5/24,5/24,5/24]].map(project);
// Enlarge and center the ordered simplex for legibility without changing its geometry.
const center=new THREE.Vector3();corners.forEach(v=>center.add(v));center.multiplyScalar(.25);function position(r){return project(r).sub(center).multiplyScalar(2.5);}
let seed=417;function rand(){seed=(1664525*seed+1013904223)>>>0;return(seed+.5)/4294967296;}
const analytic=[],periodic=[];function rational(s){const x=s.split('/').map(Number);return x.length===2?x[0]/x[1]:x[0];}
const caps=boxes.map(b=>b.caps.map(rational));const positions=[];const types=[];
for(let j=0;j<6500;j++){const r=Array.from({length:4},()=>-Math.log(rand())).sort((a,b)=>b-a);const sum=r.reduce((a,b)=>a+b);r.forEach((a,i)=>r[i]=a/sum*5/6);const p=position(r);const type=r[0]+3*r[1]<=1||2*r[0]+2*r[2]<=1||3*r[0]+r[3]<=1; (type?analytic:periodic).push(p.x,p.y,p.z);positions.push(r);types.push(type);}
function cloud(a,color,size){const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(a,3));const m=new THREE.PointsMaterial({color,size,transparent:true,opacity:.58,sizeAttenuation:true,depthWrite:false,blending:THREE.AdditiveBlending});const p=new THREE.Points(g,m);group.add(p);return p;}
cloud(analytic,0x65ddc0,.025);cloud(periodic,0xff9a60,.03);
const lines=[];for(let i=0;i<4;i++)for(let j=i+1;j<4;j++){lines.push(corners[i].clone().sub(center).multiplyScalar(2.5),corners[j].clone().sub(center).multiplyScalar(2.5));}group.add(new THREE.LineSegments(new THREE.BufferGeometry().setFromPoints(lines),new THREE.LineBasicMaterial({color:0x7a969e,transparent:true,opacity:.6})));
const selection=cloud([],0xffddae,.045);selection.material.opacity=.72;
const halo=new THREE.Mesh(new THREE.RingGeometry(2.7,2.706,140),new THREE.MeshBasicMaterial({color:0x2e555b,side:THREE.DoubleSide,transparent:true,opacity:.45}));halo.rotation.x=-Math.PI/2;halo.position.y=-1.9;scene.add(halo);
const colors=['#78dfc5','#ffab76','#b6a5f5','#9ecbe9'];let selected=0,paused=matchMedia('(prefers-reduced-motion: reduce)').matches,time=0,last=0;
function select(i){selected=i;document.querySelector('#region-id').textContent=String(i+1).padStart(2,'0')+' / 47';document.querySelector('#region').value=i;const b=boxes[i];document.querySelector('#schedule-info').textContent=b.word.length+' SLOTS / REPEAT';document.querySelector('#slots').innerHTML=b.word.map(x=>`<div class="slot" style="--c:${colors[x]}">${'ABCD'[x]}</div>`).join('');const ps=[];positions.forEach(r=>{if(r.every((v,k)=>b.closed[k]?v<=caps[i][k]:v<caps[i][k])){const p=position(r);ps.push(p.x,p.y,p.z);}});selection.geometry.dispose();selection.geometry=new THREE.BufferGeometry();selection.geometry.setAttribute('position',new THREE.Float32BufferAttribute(ps,3));}
function resize(){const w=canvas.clientWidth,h=canvas.clientHeight;renderer.setSize(w,h,false);camera.aspect=w/h;camera.updateProjectionMatrix();}new ResizeObserver(resize).observe(canvas);select(0);
document.querySelector('#region').addEventListener('input',e=>select(+e.target.value));document.querySelector('#pause').addEventListener('click',()=>{paused=!paused;document.querySelector('#pause').textContent=paused?'Resume motion':'Pause motion';});document.querySelector('#reset').addEventListener('click',()=>{camera.position.set(4,4.2,7.2);controls.target.set(.2,.35,0);select(0);});
const capture=new URLSearchParams(location.search).has('capture');if(capture)document.body.classList.add('capture');
function draw(t){group.rotation.y=.2+Math.sin(t*.12)*.45;const slot=Math.floor(t*2.5)%boxes[selected].word.length;document.querySelectorAll('.slot').forEach((s,i)=>s.classList.toggle('active',i===slot));controls.update();renderer.render(scene,camera);}
window.renderAt=t=>{const i=t<6?0:t<12?12:36;if(i!==selected)select(i);draw(t);};window.visualReady=true;
function frame(ms){const dt=Math.min((ms-last)/1000,.1);last=ms;if(!paused)time+=dt;if(!capture)draw(time);requestAnimationFrame(frame);}resize();draw(0);requestAnimationFrame(frame);
