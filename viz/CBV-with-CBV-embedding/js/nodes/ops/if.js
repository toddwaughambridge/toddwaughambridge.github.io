define(function(require) {

	var Op = require('nodes/op');
	var BoolOp = require('nodes/ops/bool');
	var Link = require('link');
	var Flag = require('token').RewriteFlag();

	class IfOp extends Op {

		constructor(active) {
			super("if", active);
		}

		copy() {
			return new IfOp(this.active);
		}

		rewrite(token) {
			var inLink = this.findLinksInto()[0];
			var outLinks = this.findLinksOutOf();

			var name = this.graph.findNodeByKey(outLinks[0].to).name;
			var keep; var del;
			if (BoolOp.parseBoolean(name)) {
				keep = 1; del = 2;
			} else {
				keep = 2; del = 1;
			}

			var newNode = this.graph.findNodeByKey(outLinks[keep].to).prinOf.filter(x => x.boxed)[0].unbox();
			inLink.changeTo(newNode.key);

			outLinks[0].delete();
			this.graph.findNodeByKey(outLinks[0].to).delete();
			outLinks[del].delete();
			this.graph.findNodeByKey(outLinks[del].to).delete();
			this.delete();

			token.rewriteFlag = Flag.SEARCH;
			return inLink;
		}

	}

	return IfOp;
});
