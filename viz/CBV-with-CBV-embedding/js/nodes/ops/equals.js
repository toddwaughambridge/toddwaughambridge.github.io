define(function(require) {

	var Op = require('nodes/op');
	var BoolOp = require('nodes/ops/bool');
	var Link = require('link');
	var Flag = require('token').RewriteFlag();

	class EqualsOp extends Op {

		constructor(active) {
			super("==", active);
		}

		copy() {
			return new EqualsOp(this.active);
		}

		rewrite(token) {
			var outLinks = this.findLinksOutOf();
			var left = this.graph.findNodeByKey(outLinks[0].to).name;
			var right = this.graph.findNodeByKey(outLinks[1].to).name;
			var b = (left == right);
			var newNode = new BoolOp(b,false).addToGroup(this.group);
			return this.activeRewrite(token,newNode);
		}

	}

	return EqualsOp;
});
